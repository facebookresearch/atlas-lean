/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthEvenOctadIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthInverseMaskAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMasks

/-! Finite selected target and source labels retain original preferred-Q sections and all central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000

/-- All pair rows and the original 63-by-64 canonical middle octad Fourier inputs. -/
def generatedAxisGlobalOddFourthSelectedTarget (j : Fin 4584) : GriessShortIndex :=
  if h : j.val < 552 then
    Sum.inl (⟨j.val / 276, by omega⟩, ⟨j.val % 276, Nat.mod_lt _ (by decide)⟩)
  else Sum.inr (Sum.inl
    (generatedAxisGlobalCanonicalFourthEvenOctadIndex ⟨(j.val-552)/64, by omega⟩,
      ⟨(j.val-552)%64, Nat.mod_lt _ (by decide)⟩))

/-- Original flat preferred-label enumeration, with all three dictionary families. -/
def generatedAxisGlobalOddFourthSelectedDecode (j : Fin 98280) : GriessShortIndex :=
  if h : j.val < 552 then
    Sum.inl (⟨j.val / 276, by omega⟩, ⟨j.val % 276, Nat.mod_lt _ (by decide)⟩)
  else if h' : j.val < 49128 then
    Sum.inr (Sum.inl (⟨(j.val-552)/64, by omega⟩,
      ⟨(j.val-552)%64, Nat.mod_lt _ (by decide)⟩))
  else Sum.inr (Sum.inr (⟨(j.val-49128)/24, by omega⟩,
    ⟨(j.val-49128)%24, Nat.mod_lt _ (by decide)⟩))

/-- Bounded lookup of the complete candidate original source labels for frame 0. -/
def generatedAxisGlobalOddFourthSelectedSourceTree00 : GeneratedAxisGlobalSparseLookupTree (Fin 98280) :=
  (.branch 2292 94980
(.branch 1146 2934
(.branch 573 33685
(.branch 286 34561
(.branch 143 33394
(.branch 71 34740
(.branch 35 9044
(.branch 17 123
(.branch 8 1155
(.branch 4 3409
(.branch 2 34572
(.branch 1 10254
(.branch 0 3537
.empty
.empty)
.empty)
(.branch 3 1164
.empty
.empty))
(.branch 6 3505
(.branch 5 3521
.empty
.empty)
(.branch 7 34574
.empty
.empty)))
(.branch 13 10255
(.branch 11 10253
(.branch 10 34573
(.branch 9 3422
.empty
.empty)
.empty)
(.branch 12 1166
.empty
.empty))
(.branch 15 1165
(.branch 14 3393
.empty
.empty)
(.branch 16 3377
.empty
.empty))))
(.branch 26 1042
(.branch 22 34563
(.branch 20 124
(.branch 19 3550
(.branch 18 401
.empty
.empty)
.empty)
(.branch 21 10240
.empty
.empty))
(.branch 24 33431
(.branch 23 9041
.empty
.empty)
(.branch 25 3479
.empty
.empty)))
(.branch 31 1029
(.branch 29 33425
(.branch 28 538
(.branch 27 255
.empty
.empty)
.empty)
(.branch 30 3467
.empty
.empty))
(.branch 33 9042
(.branch 32 33426
.empty
.empty)
(.branch 34 3473
.empty
.empty)))))
(.branch 53 33037
(.branch 44 33419
(.branch 40 3528
(.branch 38 1002
(.branch 37 3474
(.branch 36 1035
.empty
.empty)
.empty)
(.branch 39 3538
.empty
.empty))
(.branch 42 3540
(.branch 41 264
.empty
.empty)
(.branch 43 9032
.empty
.empty)))
(.branch 49 9009
(.branch 47 8977
(.branch 46 10342
(.branch 45 33036
.empty
.empty)
.empty)
(.branch 48 9025
.empty
.empty))
(.branch 51 10294
(.branch 50 33038
.empty
.empty)
(.branch 52 8990
.empty
.empty))))
(.branch 62 9054
(.branch 58 10322
(.branch 56 54
(.branch 55 10318
(.branch 54 45
.empty
.empty)
.empty)
(.branch 57 8961
.empty
.empty))
(.branch 60 10258
(.branch 59 8945
.empty
.empty)
(.branch 61 10218
.empty
.empty)))
(.branch 67 33367
(.branch 65 33027
(.branch 64 331
(.branch 63 10266
.empty
.empty)
.empty)
(.branch 66 34788
.empty
.empty))
(.branch 69 33399
(.branch 68 33415
.empty
.empty)
(.branch 70 311
.empty
.empty))))))
(.branch 107 33361
(.branch 89 34790
(.branch 80 34576
(.branch 76 33048
(.branch 74 33040
(.branch 73 289
(.branch 72 33368
.empty
.empty)
.empty)
(.branch 75 34764
.empty
.empty))
(.branch 78 34768
(.branch 77 33351
.empty
.empty)
(.branch 79 33335
.empty
.empty)))
(.branch 85 507
(.branch 83 34584
(.branch 82 33432
(.branch 81 34536
.empty
.empty)
.empty)
(.branch 84 33000
.empty
.empty))
(.branch 87 3463
(.branch 86 3607
.empty
.empty)
(.branch 88 3447
.empty
.empty))))
(.branch 98 3575
(.branch 94 385
(.branch 92 34789
(.branch 91 3608
(.branch 90 461
.empty
.empty)
.empty)
(.branch 93 10341
.empty
.empty))
(.branch 96 3591
(.branch 95 10343
.empty
.empty)
(.branch 97 367
.empty
.empty)))
(.branch 103 10280
(.branch 101 3480
(.branch 100 1128
(.branch 99 1168
.empty
.empty)
.empty)
(.branch 102 1176
.empty
.empty))
(.branch 105 1044
(.branch 104 34731
.empty
.empty)
(.branch 106 1062
.empty
.empty)))))
(.branch 125 3451
(.branch 116 543
(.branch 112 3601
(.branch 110 33362
(.branch 109 269
(.branch 108 3595
.empty
.empty)
.empty)
(.branch 111 8978
.empty
.empty))
(.branch 114 250
(.branch 113 8980
.empty
.empty)
(.branch 115 3602
.empty
.empty)))
(.branch 121 8968
(.branch 119 1046
(.branch 118 3400
(.branch 117 3410
.empty
.empty)
.empty)
(.branch 120 3412
.empty
.empty))
(.branch 123 533
(.branch 122 33355
.empty
.empty)
(.branch 124 33409
.empty
.empty))))
(.branch 134 3522
(.branch 130 9028
(.branch 128 9026
(.branch 127 33410
(.branch 126 1027
.empty
.empty)
.empty)
(.branch 129 3457
.empty
.empty))
(.branch 132 3458
(.branch 131 1037
.empty
.empty)
(.branch 133 1004
.empty
.empty)))
(.branch 139 33403
(.branch 137 3524
(.branch 136 259
(.branch 135 3512
.empty
.empty)
.empty)
(.branch 138 9016
.empty
.empty))
(.branch 141 3435
(.branch 140 33393
.empty
.empty)
(.branch 142 1009
.empty
.empty)))))))
(.branch 215 10257
(.branch 179 1151
(.branch 161 33050
(.branch 152 547
(.branch 148 3442
(.branch 146 9012
(.branch 145 3441
(.branch 144 9010
.empty
.empty)
.empty)
(.branch 147 1055
.empty
.empty))
(.branch 150 3506
(.branch 149 1022
.empty
.empty)
(.branch 151 3496
.empty
.empty)))
(.branch 157 33374
(.branch 155 33387
(.branch 154 9000
(.branch 153 3508
.empty
.empty)
.empty)
(.branch 156 34742
.empty
.empty))
(.branch 159 33042
(.branch 158 0
.empty
.empty)
(.branch 160 34766
.empty
.empty))))
(.branch 170 36
(.branch 166 34538
(.branch 164 33329
(.branch 163 34770
(.branch 162 33345
.empty
.empty)
.empty)
(.branch 165 34578
.empty
.empty))
(.branch 168 34586
(.branch 167 33438
.empty
.empty)
(.branch 169 33002
.empty
.empty)))
(.branch 175 10295
(.branch 173 10293
(.branch 172 34741
(.branch 171 3620
.empty
.empty)
.empty)
(.branch 174 110
.empty
.empty))
(.branch 177 92
(.branch 176 3579
.empty
.empty)
(.branch 178 3563
.empty
.empty)))))
(.branch 197 33380
(.branch 188 8987
(.branch 184 34779
(.branch 182 1143
(.branch 181 3492
(.branch 180 1191
.empty
.empty)
.empty)
(.branch 183 10328
.empty
.empty))
(.branch 186 8989
(.branch 185 33373
.empty
.empty)
(.branch 187 3614
.empty
.empty)))
(.branch 193 3431
(.branch 191 550
(.branch 190 3613
(.branch 189 254
.empty
.empty)
.empty)
(.branch 192 3421
.empty
.empty))
(.branch 195 3419
(.branch 194 1025
.empty
.empty)
(.branch 196 8999
.empty
.empty))))
(.branch 206 33437
(.branch 202 34769
(.branch 200 33049
(.branch 199 34765
(.branch 198 33041
.empty
.empty)
.empty)
(.branch 201 33346
.empty
.empty))
(.branch 204 34577
(.branch 203 33330
.empty
.empty)
(.branch 205 34537
.empty
.empty)))
(.branch 211 74
(.branch 209 14
(.branch 208 33001
(.branch 207 34585
.empty
.empty)
.empty)
(.branch 210 10317
.empty
.empty))
(.branch 213 10321
(.branch 212 8962
.empty
.empty)
(.branch 214 8946
.empty
.empty))))))
(.branch 251 3485
(.branch 233 8948
(.branch 224 3569
(.branch 220 33023
(.branch 218 10265
(.branch 217 9053
(.branch 216 10217
.empty
.empty)
.empty)
(.branch 219 351
.empty
.empty))
(.branch 222 3585
(.branch 221 10319
.empty
.empty)
(.branch 223 86
.empty
.empty)))
(.branch 229 10304
(.branch 227 3486
(.branch 226 1130
(.branch 225 1170
.empty
.empty)
.empty)
(.branch 228 1178
.empty
.empty))
(.branch 231 8964
(.branch 230 34755
.empty
.empty)
(.branch 232 10323
.empty
.empty))))
(.branch 242 3394
(.branch 238 486
(.branch 236 9051
(.branch 235 10219
(.branch 234 10259
.empty
.empty)
.empty)
(.branch 237 10267
.empty
.empty))
(.branch 240 3586
(.branch 239 33015
.empty
.empty)
(.branch 241 528
.empty
.empty)))
(.branch 247 33339
(.branch 245 3396
(.branch 244 1039
(.branch 243 3384
.empty
.empty)
.empty)
(.branch 246 8952
.empty
.empty))
(.branch 249 1169
(.branch 248 3570
.empty
.empty)
(.branch 250 1129
.empty
.empty)))))
(.branch 269 34599
(.branch 260 33323
(.branch 256 3368
(.branch 254 34751
(.branch 253 10300
(.branch 252 1177
.empty
.empty)
.empty)
(.branch 255 3378
.empty
.empty))
(.branch 258 3380
(.branch 257 1006
.empty
.empty)
(.branch 259 8936
.empty
.empty)))
(.branch 265 34559
(.branch 263 140
(.branch 262 3549
(.branch 261 417
.empty
.empty)
.empty)
(.branch 264 10236
.empty
.empty))
(.branch 267 432
(.branch 266 3559
.empty
.empty)
(.branch 268 10276
.empty
.empty))))
(.branch 278 34560
(.branch 274 34551
(.branch 272 33444
(.branch 271 9063
(.branch 270 3547
.empty
.empty)
.empty)
(.branch 273 10228
.empty
.empty))
(.branch 276 3534
(.branch 275 33063
.empty
.empty)
(.branch 277 10242
.empty
.empty)))
(.branch 282 3502
(.branch 280 3406
(.branch 279 1152
.empty
.empty)
(.branch 281 3518
.empty
.empty))
(.branch 284 1167
(.branch 283 34562
.empty
.empty)
(.branch 285 3425
.empty
.empty))))))))
(.branch 430 9015
(.branch 358 33447
(.branch 322 10282
(.branch 304 535
(.branch 295 3553
(.branch 291 1153
(.branch 289 10243
(.branch 288 1154
(.branch 287 10241
.empty
.empty)
.empty)
(.branch 290 3390
.empty
.empty))
(.branch 293 156
(.branch 292 3374
.empty
.empty)
(.branch 294 416
.empty
.empty)))
(.branch 300 33416
(.branch 298 34575
(.branch 297 10252
(.branch 296 141
.empty
.empty)
.empty)
(.branch 299 9038
.empty
.empty))
(.branch 302 1060
(.branch 301 3464
.empty
.empty)
(.branch 303 271
.empty
.empty))))
(.branch 313 3469
(.branch 309 9037
(.branch 307 1011
(.branch 306 3476
(.branch 305 33422
.empty
.empty)
.empty)
(.branch 308 33421
.empty
.empty))
(.branch 311 9035
(.branch 310 3470
.empty
.empty)
(.branch 312 1053
.empty
.empty)))
(.branch 318 3531
(.branch 316 3543
(.branch 315 3533
(.branch 314 1020
.empty
.empty)
.empty)
(.branch 317 257
.empty
.empty))
(.branch 320 33428
(.branch 319 9047
.empty
.empty)
(.branch 321 33024
.empty
.empty)))))
(.branch 340 350
(.branch 331 10306
(.branch 327 10330
(.branch 325 9006
(.branch 324 9022
(.branch 323 8974
.empty
.empty)
.empty)
(.branch 326 33026
.empty
.empty))
(.branch 329 33025
(.branch 328 8993
.empty
.empty)
(.branch 330 210
.empty
.empty)))
(.branch 336 10238
(.branch 334 10302
(.branch 333 8958
(.branch 332 75
.empty
.empty)
.empty)
(.branch 335 8942
.empty
.empty))
(.branch 338 9057
(.branch 337 10278
.empty
.empty)
(.branch 339 10230
.empty
.empty))))
(.branch 349 312
(.branch 345 33384
(.branch 343 33352
(.branch 342 34728
(.branch 341 33039
.empty
.empty)
.empty)
(.branch 344 33400
.empty
.empty))
(.branch 347 34776
(.branch 346 290
.empty
.empty)
(.branch 348 33383
.empty
.empty)))
(.branch 354 34748
(.branch 352 33012
(.branch 351 34752
(.branch 350 33020
.empty
.empty)
.empty)
(.branch 353 33336
.empty
.empty))
(.branch 356 34556
(.branch 355 33320
.empty
.empty)
(.branch 357 34596
.empty
.empty))))))
(.branch 394 3415
(.branch 376 1188
(.branch 367 3623
(.branch 363 3448
(.branch 361 276
(.branch 360 33060
(.branch 359 34548
.empty
.empty)
.empty)
(.branch 362 3592
.empty
.empty))
(.branch 365 34730
(.branch 364 3432
.empty
.empty)
(.branch 366 362
.empty
.empty)))
(.branch 372 3576
(.branch 370 368
(.branch 369 10281
(.branch 368 34729
.empty
.empty)
.empty)
(.branch 371 10283
.empty
.empty))
(.branch 374 3560
(.branch 373 386
.empty
.empty)
(.branch 375 1148
.empty
.empty))))
(.branch 385 252
(.branch 381 1058
(.branch 379 10340
(.branch 378 1140
(.branch 377 3495
.empty
.empty)
.empty)
(.branch 380 34791
.empty
.empty))
(.branch 383 33358
(.branch 382 1040
.empty
.empty)
(.branch 384 3604
.empty
.empty)))
(.branch 390 274
(.branch 388 3598
(.branch 387 8973
(.branch 386 33357
.empty
.empty)
.empty)
(.branch 389 8971
.empty
.empty))
(.branch 392 530
(.branch 391 3597
.empty
.empty)
(.branch 393 3405
.empty
.empty)))))
(.branch 412 262
(.branch 403 33405
(.branch 399 540
(.branch 397 8983
(.branch 396 3403
(.branch 395 1056
.empty
.empty)
.empty)
(.branch 398 33364
.empty
.empty))
(.branch 401 3460
(.branch 400 33406
.empty
.empty)
(.branch 402 1013
.empty
.empty)))
(.branch 408 3453
(.branch 406 9019
(.branch 405 3454
(.branch 404 9021
.empty
.empty)
.empty)
(.branch 407 1051
.empty
.empty))
(.branch 410 3517
(.branch 409 1018
.empty
.empty)
(.branch 411 3527
.empty
.empty))))
(.branch 421 3438
(.branch 417 3444
(.branch 415 33412
(.branch 414 9031
(.branch 413 3515
.empty
.empty)
.empty)
(.branch 416 33390
.empty
.empty))
(.branch 419 33389
(.branch 418 1031
.empty
.empty)
(.branch 420 9005
.empty
.empty)))
(.branch 426 3501
(.branch 424 3437
(.branch 423 1033
(.branch 422 9003
.empty
.empty)
.empty)
(.branch 425 1000
.empty
.empty))
(.branch 428 531
(.branch 427 3511
.empty
.empty)
(.branch 429 3499
.empty
.empty)))))))
(.branch 502 1190
(.branch 466 3618
(.branch 448 34777
(.branch 439 34750
(.branch 435 33022
(.branch 433 33377
(.branch 432 34778
(.branch 431 33396
.empty
.empty)
.empty)
(.branch 434 231
.empty
.empty))
(.branch 437 33014
(.branch 436 34754
.empty
.empty)
(.branch 438 33342
.empty
.empty)))
(.branch 444 34550
(.branch 442 34598
(.branch 441 34558
(.branch 440 33326
.empty
.empty)
.empty)
(.branch 443 33441
.empty
.empty))
(.branch 446 13
(.branch 445 33062
.empty
.empty)
(.branch 447 3611
.empty
.empty))))
(.branch 457 3483
(.branch 453 109
(.branch 451 10331
(.branch 450 91
(.branch 449 10329
.empty
.empty)
.empty)
(.branch 452 3588
.empty
.empty))
(.branch 455 1171
(.branch 454 3572
.empty
.empty)
(.branch 456 1131
.empty
.empty)))
(.branch 462 8994
(.branch 460 34743
(.branch 459 10292
(.branch 458 1179
.empty
.empty)
.empty)
(.branch 461 33378
.empty
.empty))
(.branch 464 8996
(.branch 463 3617
.empty
.empty)
(.branch 465 267
.empty
.empty)))))
(.branch 484 33061
(.branch 475 34753
(.branch 471 3428
(.branch 469 3416
(.branch 468 3426
(.branch 467 526
.empty
.empty)
.empty)
(.branch 470 1015
.empty
.empty))
(.branch 473 33371
(.branch 472 8984
.empty
.empty)
(.branch 474 33021
.empty
.empty)))
(.branch 480 34557
(.branch 478 34749
(.branch 477 33341
(.branch 476 33013
.empty
.empty)
.empty)
(.branch 479 33325
.empty
.empty))
(.branch 482 33442
(.branch 481 34597
.empty
.empty)
(.branch 483 34549
.empty
.empty))))
(.branch 493 9058
(.branch 489 10301
(.branch 487 55
(.branch 486 10305
(.branch 485 35
.empty
.empty)
.empty)
(.branch 488 8957
.empty
.empty))
(.branch 491 10237
(.branch 490 8941
.empty
.empty)
(.branch 492 10277
.empty
.empty)))
(.branch 498 3582
(.branch 496 33043
(.branch 495 330
(.branch 494 10229
.empty
.empty)
.empty)
(.branch 497 10307
.empty
.empty))
(.branch 500 3566
(.branch 499 185
.empty
.empty)
(.branch 501 1150
.empty
.empty))))))
(.branch 538 3554
(.branch 520 1049
(.branch 511 10279
(.branch 507 8955
(.branch 505 10316
(.branch 504 1142
(.branch 503 3489
.empty
.empty)
.empty)
(.branch 506 34767
.empty
.empty))
(.branch 509 8939
(.branch 508 10303
.empty
.empty)
(.branch 510 10239
.empty
.empty)))
(.branch 516 3581
(.branch 514 321
(.branch 513 10231
(.branch 512 9060
.empty
.empty)
.empty)
(.branch 515 33051
.empty
.empty))
(.branch 518 3389
(.branch 517 545
.empty
.empty)
(.branch 519 3399
.empty
.empty))))
(.branch 529 10320
(.branch 525 1149
(.branch 523 33348
(.branch 522 8967
(.branch 521 3387
.empty
.empty)
.empty)
(.branch 524 3565
.empty
.empty))
(.branch 527 3490
(.branch 526 1189
.empty
.empty)
(.branch 528 1141
.empty
.empty)))
(.branch 534 3371
(.branch 532 3383
(.branch 531 3373
(.branch 530 34771
.empty
.empty)
.empty)
(.branch 533 1016
.empty
.empty))
(.branch 536 33332
(.branch 535 8951
.empty
.empty)
(.branch 537 400
.empty
.empty)))))
(.branch 556 2956
(.branch 547 9048
(.branch 543 399
(.branch 541 34579
(.branch 540 10256
(.branch 539 125
.empty
.empty)
.empty)
(.branch 542 3544
.empty
.empty))
(.branch 545 34539
(.branch 544 10216
.empty
.empty)
(.branch 546 3556
.empty
.empty)))
(.branch 552 3052
(.branch 550 34587
(.branch 549 10264
(.branch 548 33435
.empty
.empty)
.empty)
(.branch 551 33003
.empty
.empty))
(.branch 554 3068
(.branch 553 1231
.empty
.empty)
(.branch 555 1248
.empty
.empty))))
(.branch 565 1247
(.branch 561 1600
(.branch 559 1599
(.branch 558 2979
(.branch 557 1632
.empty
.empty)
.empty)
(.branch 560 2972
.empty
.empty))
(.branch 563 1631
(.branch 562 2963
.empty
.empty)
(.branch 564 3075
.empty
.empty)))
(.branch 569 33589
(.branch 567 1232
(.branch 566 3059
.empty
.empty)
(.branch 568 34505
.empty
.empty))
(.branch 571 33605
(.branch 570 34534
.empty
.empty)
(.branch 572 34342
.empty
.empty)))))))))
(.branch 860 60921
(.branch 717 88994
(.branch 645 94662
(.branch 609 34298
(.branch 591 2976
(.branch 582 34518
(.branch 578 34329
(.branch 576 34310
(.branch 575 33690
(.branch 574 34297
.empty
.empty)
.empty)
(.branch 577 33701
.empty
.empty))
(.branch 580 34521
(.branch 579 33674
.empty
.empty)
(.branch 581 33594
.empty
.empty)))
(.branch 587 3071
(.branch 585 3055
(.branch 584 1228
(.branch 583 33578
.empty
.empty)
.empty)
(.branch 586 1251
.empty
.empty))
(.branch 589 2959
(.branch 588 1635
.empty
.empty)
(.branch 590 1596
.empty
.empty))))
(.branch 600 33577
(.branch 596 1244
(.branch 594 1628
(.branch 593 2975
(.branch 592 1603
.empty
.empty)
.empty)
(.branch 595 2960
.empty
.empty))
(.branch 598 1235
(.branch 597 3072
.empty
.empty)
(.branch 599 3056
.empty
.empty)))
(.branch 605 34330
(.branch 603 34522
(.branch 602 33593
(.branch 601 34517
.empty
.empty)
.empty)
(.branch 604 33673
.empty
.empty))
(.branch 607 34309
(.branch 606 33702
.empty
.empty)
(.branch 608 33689
.empty
.empty)))))
(.branch 627 88617
(.branch 618 93583
(.branch 614 33590
(.branch 612 33606
(.branch 611 34341
(.branch 610 33686
.empty
.empty)
.empty)
(.branch 613 34533
.empty
.empty))
(.branch 616 94568
(.branch 615 34506
.empty
.empty)
(.branch 617 94569
.empty
.empty)))
(.branch 623 88665
(.branch 621 87294
(.branch 620 87295
(.branch 619 93582
.empty
.empty)
.empty)
(.branch 622 88664
.empty
.empty))
(.branch 625 87246
(.branch 624 87247
.empty
.empty)
(.branch 626 88616
.empty
.empty))))
(.branch 636 87344
(.branch 632 94711
(.branch 630 93631
(.branch 629 94617
(.branch 628 94616
.empty
.empty)
.empty)
(.branch 631 93630
.empty
.empty))
(.branch 634 93344
(.branch 633 94710
.empty
.empty)
(.branch 635 93345
.empty
.empty)))
(.branch 641 87393
(.branch 639 88326
(.branch 638 88327
(.branch 637 87345
.empty
.empty)
.empty)
(.branch 640 87392
.empty
.empty))
(.branch 643 88374
(.branch 642 88375
.empty
.empty)
(.branch 644 94663
.empty
.empty))))))
(.branch 681 93252
(.branch 663 94713
(.branch 654 87391
(.branch 650 94664
(.branch 648 93295
(.branch 647 93297
(.branch 646 93296
.empty
.empty)
.empty)
(.branch 649 93294
.empty
.empty))
(.branch 652 88376
(.branch 651 94665
.empty
.empty)
(.branch 653 88377
.empty
.empty)))
(.branch 659 87342
(.branch 657 88329
(.branch 656 88328
(.branch 655 87390
.empty
.empty)
.empty)
(.branch 658 87343
.empty
.empty))
(.branch 661 93342
(.branch 660 93343
.empty
.empty)
(.branch 662 94712
.empty
.empty))))
(.branch 672 88663
(.branch 668 88615
(.branch 666 94615
(.branch 665 93633
(.branch 664 93632
.empty
.empty)
.empty)
(.branch 667 94614
.empty
.empty))
(.branch 670 87248
(.branch 669 88614
.empty
.empty)
(.branch 671 87249
.empty
.empty)))
(.branch 677 93585
(.branch 675 87297
(.branch 674 87296
(.branch 673 88662
.empty
.empty)
.empty)
(.branch 676 93584
.empty
.empty))
(.branch 679 94566
(.branch 678 94567
.empty
.empty)
(.branch 680 93242
.empty
.empty)))))
(.branch 699 95052
(.branch 690 94946
(.branch 686 88764
(.branch 684 93243
(.branch 683 88755
(.branch 682 88765
.empty
.empty)
.empty)
(.branch 685 93253
.empty
.empty))
(.branch 688 86965
(.branch 687 88754
.empty
.empty)
(.branch 689 86955
.empty
.empty)))
(.branch 695 94957
(.branch 693 86954
(.branch 692 86964
(.branch 691 94956
.empty
.empty)
.empty)
(.branch 694 94947
.empty
.empty))
(.branch 697 86859
(.branch 696 86869
.empty
.empty)
(.branch 698 95042
.empty
.empty))))
(.branch 708 92955
(.branch 704 92954
(.branch 702 95043
(.branch 701 86858
(.branch 700 86868
.empty
.empty)
.empty)
(.branch 703 95053
.empty
.empty))
(.branch 706 89053
(.branch 705 92964
.empty
.empty)
(.branch 707 89043
.empty
.empty)))
(.branch 713 88995
(.branch 711 89042
(.branch 710 89052
(.branch 709 92965
.empty
.empty)
.empty)
(.branch 712 89005
.empty
.empty))
(.branch 715 92916
(.branch 714 92906
.empty
.empty)
(.branch 716 89004
.empty
.empty)))))))
(.branch 789 55203
(.branch 753 59460
(.branch 735 87002
(.branch 726 86916
(.branch 722 86917
(.branch 720 95090
(.branch 719 92917
(.branch 718 92907
.empty
.empty)
.empty)
(.branch 721 95100
.empty
.empty))
(.branch 724 95091
(.branch 723 86907
.empty
.empty)
(.branch 725 95101
.empty
.empty)))
(.branch 731 87003
(.branch 729 95004
(.branch 728 94994
(.branch 727 86906
.empty
.empty)
.empty)
(.branch 730 87013
.empty
.empty))
(.branch 733 95005
(.branch 732 94995
.empty
.empty)
(.branch 734 87012
.empty
.empty))))
(.branch 744 59172
(.branch 740 88716
(.branch 738 93194
(.branch 737 88707
(.branch 736 88717
.empty
.empty)
.empty)
(.branch 739 93204
.empty
.empty))
(.branch 742 93195
(.branch 741 88706
.empty
.empty)
(.branch 743 93205
.empty
.empty)))
(.branch 749 53163
(.branch 747 53162
(.branch 746 59163
(.branch 745 53173
.empty
.empty)
.empty)
(.branch 748 59162
.empty
.empty))
(.branch 751 53172
(.branch 750 59173
.empty
.empty)
(.branch 752 53077
.empty
.empty)))))
(.branch 771 54962
(.branch 762 55250
(.branch 758 53076
(.branch 756 53067
(.branch 755 59451
(.branch 754 53066
.empty
.empty)
.empty)
(.branch 757 59450
.empty
.empty))
(.branch 760 55261
(.branch 759 59461
.empty
.empty)
(.branch 761 61164
.empty
.empty)))
(.branch 767 61165
(.branch 765 61154
(.branch 764 55251
(.branch 763 61155
.empty
.empty)
.empty)
(.branch 766 55260
.empty
.empty))
(.branch 769 54973
(.branch 768 61260
.empty
.empty)
(.branch 770 61251
.empty
.empty))))
(.branch 780 54915
(.branch 776 54925
(.branch 774 61261
(.branch 773 54963
(.branch 772 61250
.empty
.empty)
.empty)
(.branch 775 54972
.empty
.empty))
(.branch 778 54914
(.branch 777 61308
.empty
.empty)
(.branch 779 61299
.empty
.empty)))
(.branch 785 55213
(.branch 783 61309
(.branch 782 54924
(.branch 781 61298
.empty
.empty)
.empty)
(.branch 784 61212
.empty
.empty))
(.branch 787 55202
(.branch 786 61203
.empty
.empty)
(.branch 788 61202
.empty
.empty))))))
(.branch 825 59790
(.branch 807 59125
(.branch 798 59413
(.branch 794 59403
(.branch 792 59412
(.branch 791 55212
(.branch 790 61213
.empty
.empty)
.empty)
(.branch 793 53125
.empty
.empty))
(.branch 796 59402
(.branch 795 53114
.empty
.empty)
(.branch 797 53115
.empty
.empty)))
(.branch 803 59115
(.branch 801 59124
(.branch 800 53221
(.branch 799 53124
.empty
.empty)
.empty)
(.branch 802 53210
.empty
.empty))
(.branch 805 59114
(.branch 804 53211
.empty
.empty)
(.branch 806 53220
.empty
.empty))))
(.branch 816 54583
(.branch 812 59839
(.branch 810 54535
(.branch 809 59502
(.branch 808 60871
.empty
.empty)
.empty)
(.branch 811 53550
.empty
.empty))
(.branch 814 53503
(.branch 813 60822
.empty
.empty)
(.branch 815 54870
.empty
.empty)))
(.branch 821 54822
(.branch 819 59550
(.branch 818 60919
(.branch 817 53598
.empty
.empty)
.empty)
(.branch 820 53455
.empty
.empty))
(.branch 823 60774
(.branch 822 59791
.empty
.empty)
(.branch 824 60775
.empty
.empty)))))
(.branch 843 54536
(.branch 834 60823
(.branch 830 53599
(.branch 828 59551
(.branch 827 53454
(.branch 826 54823
.empty
.empty)
.empty)
(.branch 829 60918
.empty
.empty))
(.branch 832 54871
(.branch 831 54582
.empty
.empty)
(.branch 833 53502
.empty
.empty)))
(.branch 839 60870
(.branch 837 54534
(.branch 836 53551
(.branch 835 59838
.empty
.empty)
.empty)
(.branch 838 59503
.empty
.empty))
(.branch 841 60872
(.branch 840 59505
.empty
.empty)
(.branch 842 53553
.empty
.empty))))
(.branch 852 54825
(.branch 848 53601
(.branch 846 54873
(.branch 845 59840
(.branch 844 60825
.empty
.empty)
.empty)
(.branch 847 53504
.empty
.empty))
(.branch 850 59553
(.branch 849 54584
.empty
.empty)
(.branch 851 60920
.empty
.empty)))
(.branch 856 59793
(.branch 854 60777
(.branch 853 53456
.empty
.empty)
(.branch 855 59792
.empty
.empty))
(.branch 858 53457
(.branch 857 60776
.empty
.empty)
(.branch 859 54824
.empty
.empty))))))))
(.branch 1003 53142
(.branch 932 93372
(.branch 896 93612
(.branch 878 94586
(.branch 869 53552
(.branch 865 54872
(.branch 863 53600
(.branch 862 54585
(.branch 861 59552
.empty
.empty)
.empty)
(.branch 864 53505
.empty
.empty))
(.branch 867 60824
(.branch 866 59841
.empty
.empty)
(.branch 868 54537
.empty
.empty)))
(.branch 874 87420
(.branch 872 87411
(.branch 871 59504
(.branch 870 60873
.empty
.empty)
.empty)
(.branch 873 93325
.empty
.empty))
(.branch 876 94597
(.branch 875 93314
.empty
.empty)
(.branch 877 88587
.empty
.empty))))
(.branch 887 88597
(.branch 883 93315
(.branch 881 93324
(.branch 880 87410
(.branch 879 88596
.empty
.empty)
.empty)
(.branch 882 87421
.empty
.empty))
(.branch 885 88586
(.branch 884 94596
.empty
.empty)
(.branch 886 94587
.empty
.empty)))
(.branch 892 88299
(.branch 890 93602
(.branch 889 87315
(.branch 888 93613
.empty
.empty)
.empty)
(.branch 891 87324
.empty
.empty))
(.branch 894 88308
(.branch 893 94693
.empty
.empty)
(.branch 895 94682
.empty
.empty)))))
(.branch 914 94635
(.branch 905 88347
(.branch 901 94692
(.branch 899 87325
(.branch 898 93603
(.branch 897 87314
.empty
.empty)
.empty)
(.branch 900 88298
.empty
.empty))
(.branch 903 94683
(.branch 902 88309
.empty
.empty)
(.branch 904 94645
.empty
.empty)))
(.branch 910 87276
(.branch 908 87267
(.branch 907 88356
(.branch 906 94634
.empty
.empty)
.empty)
(.branch 909 93661
.empty
.empty))
(.branch 912 94644
(.branch 911 93650
.empty
.empty)
(.branch 913 88346
.empty
.empty))))
(.branch 923 94538
(.branch 919 93651
(.branch 917 93660
(.branch 916 87266
(.branch 915 88357
.empty
.empty)
.empty)
(.branch 918 87277
.empty
.empty))
(.branch 921 94549
(.branch 920 88635
.empty
.empty)
(.branch 922 88644
.empty
.empty)))
(.branch 928 88634
(.branch 926 93362
(.branch 925 87363
(.branch 924 93373
.empty
.empty)
.empty)
(.branch 927 87372
.empty
.empty))
(.branch 930 88645
(.branch 929 94548
.empty
.empty)
(.branch 931 94539
.empty
.empty))))))
(.branch 968 86983
(.branch 950 89025
(.branch 941 92982
(.branch 937 86982
(.branch 935 87373
(.branch 934 93363
(.branch 933 87362
.empty
.empty)
.empty)
(.branch 936 88689
.empty
.empty))
(.branch 939 92934
(.branch 938 95025
.empty
.empty)
(.branch 940 95073
.empty
.empty)))
(.branch 946 94929
(.branch 944 88977
(.branch 943 87030
(.branch 942 88737
.empty
.empty)
.empty)
(.branch 945 86886
.empty
.empty))
(.branch 948 94977
(.branch 947 93222
.empty
.empty)
(.branch 949 93270
.empty
.empty))))
(.branch 959 88974
(.branch 955 94974
(.branch 953 89022
(.branch 952 86937
(.branch 951 86934
.empty
.empty)
.empty)
(.branch 954 93273
.empty
.empty))
(.branch 957 94926
(.branch 956 93225
.empty
.empty)
(.branch 958 86889
.empty
.empty)))
(.branch 964 92937
(.branch 962 92985
(.branch 961 88734
(.branch 960 87033
.empty
.empty)
.empty)
(.branch 963 95070
.empty
.empty))
(.branch 966 86985
(.branch 965 95022
.empty
.empty)
(.branch 967 88686
.empty
.empty)))))
(.branch 986 94975
(.branch 977 88976
(.branch 973 95072
(.branch 971 95024
(.branch 970 92935
(.branch 969 88688
.empty
.empty)
.empty)
(.branch 972 92983
.empty
.empty))
(.branch 975 88736
(.branch 974 87031
.empty
.empty)
(.branch 976 86887
.empty
.empty)))
(.branch 982 86935
(.branch 980 93271
(.branch 979 94928
(.branch 978 93223
.empty
.empty)
.empty)
(.branch 981 94976
.empty
.empty))
(.branch 984 89023
(.branch 983 89024
.empty
.empty)
(.branch 985 86936
.empty
.empty))))
(.branch 995 92984
(.branch 991 86888
(.branch 989 93224
(.branch 988 94927
(.branch 987 93272
.empty
.empty)
.empty)
(.branch 990 88975
.empty
.empty))
(.branch 993 87032
(.branch 992 88735
.empty
.empty)
(.branch 994 95071
.empty
.empty)))
(.branch 999 86984
(.branch 997 92936
(.branch 996 95023
.empty
.empty)
(.branch 998 88687
.empty
.empty))
(.branch 1001 61184
(.branch 1000 59478
.empty
.empty)
(.branch 1002 55232
.empty
.empty)))))))
(.branch 1075 59811
(.branch 1039 53193
(.branch 1021 61233
(.branch 1012 61134
(.branch 1008 61280
(.branch 1006 54894
(.branch 1005 61230
(.branch 1004 59144
.empty
.empty)
.empty)
(.branch 1007 53192
.empty
.empty))
(.branch 1010 53238
(.branch 1009 59190
.empty
.empty)
(.branch 1011 54944
.empty
.empty)))
(.branch 1017 61183
(.branch 1015 55182
(.branch 1014 53096
(.branch 1013 59432
.empty
.empty)
.empty)
(.branch 1016 59481
.empty
.empty))
(.branch 1019 53145
(.branch 1018 55231
.empty
.empty)
(.branch 1020 59143
.empty
.empty))))
(.branch 1030 53095
(.branch 1026 53241
(.branch 1024 61279
(.branch 1023 53191
(.branch 1022 54897
.empty
.empty)
.empty)
(.branch 1025 59193
.empty
.empty))
(.branch 1028 61137
(.branch 1027 54943
.empty
.empty)
(.branch 1029 59431
.empty
.empty)))
(.branch 1035 53143
(.branch 1033 61185
(.branch 1032 59479
(.branch 1031 55185
.empty
.empty)
.empty)
(.branch 1034 55233
.empty
.empty))
(.branch 1037 61231
(.branch 1036 59145
.empty
.empty)
(.branch 1038 54895
.empty
.empty)))))
(.branch 1057 59192
(.branch 1048 59480
(.branch 1044 61135
(.branch 1042 53239
(.branch 1041 59191
(.branch 1040 61281
.empty
.empty)
.empty)
(.branch 1043 54945
.empty
.empty))
(.branch 1046 53097
(.branch 1045 59433
.empty
.empty)
(.branch 1047 55183
.empty
.empty)))
(.branch 1053 61232
(.branch 1051 53144
(.branch 1050 55230
(.branch 1049 61182
.empty
.empty)
.empty)
(.branch 1052 59142
.empty
.empty))
(.branch 1055 53190
(.branch 1054 54896
.empty
.empty)
(.branch 1056 61278
.empty
.empty))))
(.branch 1066 54842
(.branch 1062 53094
(.branch 1060 61136
(.branch 1059 54942
(.branch 1058 53240
.empty
.empty)
.empty)
(.branch 1061 59430
.empty
.empty))
(.branch 1064 60757
(.branch 1063 55184
.empty
.empty)
(.branch 1065 59821
.empty
.empty)))
(.branch 1071 59820
(.branch 1069 53523
(.branch 1068 54843
(.branch 1067 53522
.empty
.empty)
.empty)
(.branch 1070 60756
.empty
.empty))
(.branch 1073 53532
(.branch 1072 54852
.empty
.empty)
(.branch 1074 60747
.empty
.empty))))))
(.branch 1111 53629
(.branch 1093 60890
(.branch 1084 53571
(.branch 1080 59581
(.branch 1078 54853
(.branch 1077 59810
(.branch 1076 60746
.empty
.empty)
.empty)
(.branch 1079 53533
.empty
.empty))
(.branch 1082 53570
(.branch 1081 60901
.empty
.empty)
(.branch 1083 54506
.empty
.empty)))
(.branch 1089 54516
(.branch 1087 60900
(.branch 1086 59580
(.branch 1085 54507
.empty
.empty)
.empty)
(.branch 1088 53580
.empty
.empty))
(.branch 1091 60891
(.branch 1090 59571
.empty
.empty)
(.branch 1092 59570
.empty
.empty))))
(.branch 1102 60852
(.branch 1098 54554
(.branch 1096 60853
(.branch 1095 54517
(.branch 1094 53581
.empty
.empty)
.empty)
(.branch 1097 59533
.empty
.empty))
(.branch 1100 54555
(.branch 1099 53618
.empty
.empty)
(.branch 1101 53619
.empty
.empty)))
(.branch 1107 59523
(.branch 1105 53628
(.branch 1104 54564
(.branch 1103 59532
.empty
.empty)
.empty)
(.branch 1106 60843
.empty
.empty))
(.branch 1109 59522
(.branch 1108 60842
.empty
.empty)
(.branch 1110 54565
.empty
.empty)))))
(.branch 1129 33660
(.branch 1120 53484
(.branch 1116 53475
(.branch 1114 53474
(.branch 1113 60805
(.branch 1112 59869
.empty
.empty)
.empty)
(.branch 1115 54794
.empty
.empty))
(.branch 1118 59868
(.branch 1117 54795
.empty
.empty)
(.branch 1119 60804
.empty
.empty)))
(.branch 1125 60794
(.branch 1123 60795
(.branch 1122 59859
(.branch 1121 54804
.empty
.empty)
.empty)
(.branch 1124 59858
.empty
.empty))
(.branch 1127 54805
(.branch 1126 53485
.empty
.empty)
(.branch 1128 33644
.empty
.empty))))
(.branch 1138 1589
(.branch 1134 2933
(.branch 1132 34492
(.branch 1131 1205
(.branch 1130 1221
.empty
.empty)
.empty)
(.branch 1133 34476
.empty
.empty))
(.branch 1136 33612
(.branch 1135 2949
.empty
.empty)
(.branch 1137 33635
.empty
.empty)))
(.branch 1142 3093
(.branch 1140 34284
(.branch 1139 1621
.empty
.empty)
(.branch 1141 34316
.empty
.empty))
(.branch 1144 34496
(.branch 1143 3098
.empty
.empty)
(.branch 1145 34480
.empty
.empty))))))))))
(.branch 1719 88621
(.branch 1433 34704
(.branch 1290 25697
(.branch 1218 10222
(.branch 1182 1609
(.branch 1164 34323
(.branch 1155 3097
(.branch 1151 1206
(.branch 1149 33664
(.branch 1148 33648
(.branch 1147 2950
.empty
.empty)
.empty)
(.branch 1150 1222
.empty
.empty))
(.branch 1153 34320
(.branch 1152 34288
.empty
.empty)
(.branch 1154 3094
.empty
.empty)))
(.branch 1160 33628
(.branch 1158 1590
(.branch 1157 33631
(.branch 1156 33616
.empty
.empty)
.empty)
(.branch 1159 1622
.empty
.empty))
(.branch 1162 1610
(.branch 1161 33619
.empty
.empty)
(.branch 1163 1578
.empty
.empty))))
(.branch 1173 34499
(.branch 1169 33651
(.branch 1167 3082
(.branch 1166 3109
(.branch 1165 34291
.empty
.empty)
.empty)
(.branch 1168 33667
.empty
.empty))
(.branch 1171 1210
(.branch 1170 1194
.empty
.empty)
(.branch 1172 34483
.empty
.empty)))
(.branch 1178 3110
(.branch 1176 34319
(.branch 1175 2922
(.branch 1174 2938
.empty
.empty)
.empty)
(.branch 1177 34287
.empty
.empty))
(.branch 1180 33632
(.branch 1179 3081
.empty
.empty)
(.branch 1181 33615
.empty
.empty)))))
(.branch 1200 435
(.branch 1191 1209
(.branch 1187 2921
(.branch 1185 34495
(.branch 1184 34479
(.branch 1183 1577
.empty
.empty)
.empty)
(.branch 1186 2937
.empty
.empty))
(.branch 1189 33647
(.branch 1188 33663
.empty
.empty)
(.branch 1190 1193
.empty
.empty)))
(.branch 1196 346
(.branch 1194 326
(.branch 1193 10271
(.branch 1192 10247
.empty
.empty)
.empty)
(.branch 1195 324
.empty
.empty))
(.branch 1198 10248
(.branch 1197 344
.empty
.empty)
(.branch 1199 10224
.empty
.empty))))
(.branch 1209 10263
(.branch 1205 10225
(.branch 1203 10226
(.branch 1202 10250
(.branch 1201 404
.empty
.empty)
.empty)
(.branch 1204 10249
.empty
.empty))
(.branch 1207 405
(.branch 1206 436
.empty
.empty)
(.branch 1208 10275
.empty
.empty)))
(.branch 1214 10220
(.branch 1212 345
(.branch 1211 327
(.branch 1210 325
.empty
.empty)
.empty)
(.branch 1213 347
.empty
.empty))
(.branch 1216 420
(.branch 1215 10232
.empty
.empty)
(.branch 1217 449
.empty
.empty))))))
(.branch 1254 129
(.branch 1236 10261
(.branch 1227 49
(.branch 1223 450
(.branch 1221 10233
(.branch 1220 10221
(.branch 1219 10234
.empty
.empty)
.empty)
(.branch 1222 421
.empty
.empty))
(.branch 1225 10223
(.branch 1224 10235
.empty
.empty)
(.branch 1226 51
.empty
.empty)))
(.branch 1232 173
(.branch 1230 10260
(.branch 1229 69
(.branch 1228 71
.empty
.empty)
.empty)
(.branch 1231 10272
.empty
.empty))
(.branch 1234 10262
(.branch 1233 144
.empty
.empty)
(.branch 1235 10274
.empty
.empty))))
(.branch 1245 70
(.branch 1241 10251
(.branch 1239 145
(.branch 1238 174
(.branch 1237 10273
.empty
.empty)
.empty)
(.branch 1240 10227
.empty
.empty))
(.branch 1243 50
(.branch 1242 48
.empty
.empty)
(.branch 1244 68
.empty
.empty)))
(.branch 1250 10270
(.branch 1248 128
(.branch 1247 10244
(.branch 1246 10268
.empty
.empty)
.empty)
(.branch 1249 159
.empty
.empty))
(.branch 1252 10269
(.branch 1251 10246
.empty
.empty)
(.branch 1253 10245
.empty
.empty)))))
(.branch 1272 47887
(.branch 1263 25694
(.branch 1259 25703
(.branch 1257 47680
(.branch 1256 48932
(.branch 1255 160
.empty
.empty)
.empty)
(.branch 1258 31710
.empty
.empty))
(.branch 1261 47716
(.branch 1260 48896
.empty
.empty)
(.branch 1262 31719
.empty
.empty)))
(.branch 1268 47908
(.branch 1266 26727
(.branch 1265 48740
(.branch 1264 47872
.empty
.empty)
.empty)
(.branch 1267 30814
.empty
.empty))
(.branch 1270 26718
(.branch 1269 48704
.empty
.empty)
(.branch 1271 30823
.empty
.empty))))
(.branch 1281 47695
(.branch 1277 48719
(.branch 1275 30769
(.branch 1274 26664
(.branch 1273 48683
.empty
.empty)
.empty)
(.branch 1276 47851
.empty
.empty))
(.branch 1279 30760
(.branch 1278 26673
.empty
.empty)
(.branch 1280 48875
.empty
.empty)))
(.branch 1286 31656
(.branch 1284 48911
(.branch 1283 25640
(.branch 1282 31665
.empty
.empty)
.empty)
(.branch 1285 47659
.empty
.empty))
(.branch 1288 47656
(.branch 1287 25649
.empty
.empty)
(.branch 1289 48908
.empty
.empty)))))))
(.branch 1362 32018
(.branch 1326 26972
(.branch 1308 48743
(.branch 1299 26721
(.branch 1295 31713
(.branch 1293 48872
(.branch 1292 47692
(.branch 1291 31704
.empty
.empty)
.empty)
(.branch 1294 25688
.empty
.empty))
(.branch 1297 47848
(.branch 1296 48716
.empty
.empty)
(.branch 1298 30808
.empty
.empty)))
(.branch 1304 48707
(.branch 1302 30817
(.branch 1301 47884
(.branch 1300 48680
.empty
.empty)
.empty)
(.branch 1303 26712
.empty
.empty))
(.branch 1306 30775
(.branch 1305 47911
.empty
.empty)
(.branch 1307 26670
.empty
.empty))))
(.branch 1317 48935
(.branch 1313 48899
(.branch 1311 26679
(.branch 1310 30766
(.branch 1309 47875
.empty
.empty)
.empty)
(.branch 1312 47719
.empty
.empty))
(.branch 1315 31671
(.branch 1314 25646
.empty
.empty)
(.branch 1316 47683
.empty
.empty)))
(.branch 1322 25331
(.branch 1320 30556
(.branch 1319 31662
(.branch 1318 25655
.empty
.empty)
.empty)
(.branch 1321 30515
.empty
.empty))
(.branch 1324 32243
(.branch 1323 25372
.empty
.empty)
(.branch 1325 32284
.empty
.empty)))))
(.branch 1344 26939
(.branch 1335 32253
(.branch 1331 30546
(.branch 1329 25341
(.branch 1328 25362
(.branch 1327 26931
.empty
.empty)
.empty)
(.branch 1330 30525
.empty
.empty))
(.branch 1333 26962
(.branch 1332 26941
.empty
.empty)
(.branch 1334 32274
.empty
.empty)))
(.branch 1340 30548
(.branch 1338 26970
(.branch 1337 32282
(.branch 1336 32245
.empty
.empty)
.empty)
(.branch 1339 26933
.empty
.empty))
(.branch 1342 25339
(.branch 1341 30523
.empty
.empty)
(.branch 1343 25364
.empty
.empty))))
(.branch 1353 32028
(.branch 1349 25333
(.branch 1347 32251
(.branch 1346 32276
(.branch 1345 26964
.empty
.empty)
.empty)
(.branch 1348 25370
.empty
.empty))
(.branch 1351 30554
(.branch 1350 30517
.empty
.empty)
(.branch 1352 31987
.empty
.empty)))
(.branch 1358 25523
(.branch 1356 30492
(.branch 1355 27059
(.branch 1354 27100
.empty
.empty)
.empty)
(.branch 1357 30451
.empty
.empty))
(.branch 1360 27069
(.branch 1359 25564
.empty
.empty)
(.branch 1361 27090
.empty
.empty))))))
(.branch 1398 10387
(.branch 1380 27061
(.branch 1371 25562
(.branch 1367 30482
(.branch 1365 25533
(.branch 1364 25554
(.branch 1363 31997
.empty
.empty)
.empty)
(.branch 1366 30461
.empty
.empty))
(.branch 1369 30453
(.branch 1368 30490
.empty
.empty)
(.branch 1370 25525
.empty
.empty)))
(.branch 1376 25556
(.branch 1374 27092
(.branch 1373 32020
(.branch 1372 31995
.empty
.empty)
.empty)
(.branch 1375 27067
.empty
.empty))
(.branch 1378 30459
(.branch 1377 25531
.empty
.empty)
(.branch 1379 30484
.empty
.empty))))
(.branch 1389 33220
(.branch 1385 34620
(.branch 1383 31989
(.branch 1382 32026
(.branch 1381 27098
.empty
.empty)
.empty)
(.branch 1384 32964
.empty
.empty))
(.branch 1387 10192
(.branch 1386 610
.empty
.empty)
(.branch 1388 34684
.empty
.empty)))
(.branch 1394 562
(.branch 1392 32952
(.branch 1391 1122
(.branch 1390 10384
.empty
.empty)
.empty)
(.branch 1393 34643
.empty
.empty))
(.branch 1396 34707
(.branch 1395 10195
.empty
.empty)
(.branch 1397 33208
.empty
.empty)))))
(.branch 1416 34624
(.branch 1407 10176
(.branch 1403 1121
(.branch 1401 33236
(.branch 1400 34688
(.branch 1399 1074
.empty
.empty)
.empty)
(.branch 1402 10380
.empty
.empty))
(.branch 1405 34636
(.branch 1404 32971
.empty
.empty)
(.branch 1406 606
.empty
.empty)))
(.branch 1412 32983
(.branch 1410 10383
(.branch 1409 33224
(.branch 1408 34703
.empty
.empty)
.empty)
(.branch 1411 1073
.empty
.empty))
(.branch 1414 558
(.branch 1413 34627
.empty
.empty)
(.branch 1415 10179
.empty
.empty))))
(.branch 1425 32968
(.branch 1421 34700
(.branch 1419 609
(.branch 1418 10188
(.branch 1417 32980
.empty
.empty)
.empty)
(.branch 1420 33227
.empty
.empty))
(.branch 1423 10368
(.branch 1422 1118
.empty
.empty)
(.branch 1424 34639
.empty
.empty)))
(.branch 1429 34691
(.branch 1427 561
(.branch 1426 10191
.empty
.empty)
(.branch 1428 33239
.empty
.empty))
(.branch 1431 10371
(.branch 1430 1070
.empty
.empty)
(.branch 1432 33211
.empty
.empty))))))))
(.branch 1576 48651
(.branch 1505 1283
(.branch 1469 10089
(.branch 1451 9909
(.branch 1442 1069
(.branch 1438 10172
(.branch 1436 34640
(.branch 1435 10364
(.branch 1434 1117
.empty
.empty)
.empty)
(.branch 1437 32955
.empty
.empty))
(.branch 1440 33223
(.branch 1439 605
.empty
.empty)
(.branch 1441 34687
.empty
.empty)))
(.branch 1447 557
(.branch 1445 32967
(.branch 1444 34623
(.branch 1443 10367
.empty
.empty)
.empty)
(.branch 1446 10175
.empty
.empty))
(.branch 1449 3007
(.branch 1448 2991
.empty
.empty)
(.branch 1450 9925
.empty
.empty))))
(.branch 1460 10102
(.branch 1456 2895
(.branch 1454 2995
(.branch 1453 9910
(.branch 1452 9926
.empty
.empty)
.empty)
(.branch 1455 3011
.empty
.empty))
(.branch 1458 10101
(.branch 1457 2912
.empty
.empty)
(.branch 1459 10133
.empty
.empty)))
(.branch 1465 2896
(.branch 1463 2908
(.branch 1462 2899
(.branch 1461 10134
.empty
.empty)
.empty)
(.branch 1464 2911
.empty
.empty))
(.branch 1467 10090
(.branch 1466 10122
.empty
.empty)
(.branch 1468 10121
.empty
.empty)))))
(.branch 1487 1264
(.branch 1478 3004
(.branch 1474 9898
(.branch 1472 3008
(.branch 1471 2892
(.branch 1470 2915
.empty
.empty)
.empty)
(.branch 1473 2992
.empty
.empty))
(.branch 1476 9897
(.branch 1475 9914
.empty
.empty)
(.branch 1477 9913
.empty
.empty)))
(.branch 1483 9273
(.branch 1481 1260
(.branch 1480 1276
(.branch 1479 2988
.empty
.empty)
.empty)
(.branch 1482 9257
.empty
.empty))
(.branch 1485 9274
(.branch 1484 9258
.empty
.empty)
(.branch 1486 1280
.empty
.empty))))
(.branch 1496 1683
(.branch 1492 9226
(.branch 1490 9225
(.branch 1489 1676
(.branch 1488 1644
.empty
.empty)
.empty)
(.branch 1491 9254
.empty
.empty))
(.branch 1494 1648
(.branch 1493 9253
.empty
.empty)
(.branch 1495 1680
.empty
.empty)))
(.branch 1501 9237
(.branch 1499 9238
(.branch 1498 9241
(.branch 1497 1651
.empty
.empty)
.empty)
(.branch 1500 9242
.empty
.empty))
(.branch 1503 1647
(.branch 1502 1679
.empty
.empty)
(.branch 1504 1267
.empty
.empty))))))
(.branch 1541 30875
(.branch 1523 26645
(.branch 1514 25621
(.branch 1510 1263
(.branch 1508 9285
(.branch 1507 9270
(.branch 1506 9286
.empty
.empty)
.empty)
(.branch 1509 9269
.empty
.empty))
(.branch 1512 31763
(.branch 1511 1279
.empty
.empty)
(.branch 1513 31765
.empty
.empty)))
(.branch 1519 25883
(.branch 1517 31955
(.branch 1516 31963
(.branch 1515 25619
.empty
.empty)
.empty)
(.branch 1518 25875
.empty
.empty))
(.branch 1521 30867
(.branch 1520 30869
.empty
.empty)
(.branch 1522 26643
.empty
.empty))))
(.branch 1532 31771
(.branch 1528 31965
(.branch 1526 26779
(.branch 1525 30939
(.branch 1524 30931
.empty
.empty)
.empty)
(.branch 1527 26771
.empty
.empty))
(.branch 1530 25877
(.branch 1529 31957
.empty
.empty)
(.branch 1531 25885
.empty
.empty)))
(.branch 1537 30941
(.branch 1535 25627
(.branch 1534 25629
(.branch 1533 31773
.empty
.empty)
.empty)
(.branch 1536 30933
.empty
.empty))
(.branch 1539 26773
(.branch 1538 26781
.empty
.empty)
(.branch 1540 30877
.empty
.empty)))))
(.branch 1559 25844
(.branch 1550 26740
(.branch 1546 26620
(.branch 1544 30842
(.branch 1543 26653
(.branch 1542 26651
.empty
.empty)
.empty)
(.branch 1545 30844
.empty
.empty))
(.branch 1548 30908
(.branch 1547 26618
.empty
.empty)
(.branch 1549 30900
.empty
.empty)))
(.branch 1555 25596
(.branch 1553 31738
(.branch 1552 31740
(.branch 1551 26748
.empty
.empty)
.empty)
(.branch 1554 25594
.empty
.empty))
(.branch 1557 31932
(.branch 1556 31924
.empty
.empty)
(.branch 1558 25852
.empty
.empty))))
(.branch 1568 31922
(.branch 1564 30834
(.branch 1562 26738
(.branch 1561 30898
(.branch 1560 30906
.empty
.empty)
.empty)
(.branch 1563 26746
.empty
.empty))
(.branch 1566 26612
(.branch 1565 30836
.empty
.empty)
(.branch 1567 26610
.empty
.empty)))
(.branch 1572 31732
(.branch 1570 25850
(.branch 1569 31930
.empty
.empty)
(.branch 1571 25842
.empty
.empty))
(.branch 1574 25586
(.branch 1573 31730
.empty
.empty)
(.branch 1575 25588
.empty
.empty)))))))
(.branch 1648 92960
(.branch 1612 47971
(.branch 1594 26992
(.branch 1585 47599
(.branch 1581 47627
(.branch 1579 25264
(.branch 1578 25311
(.branch 1577 48644
.empty
.empty)
.empty)
(.branch 1580 47620
.empty
.empty))
(.branch 1583 30623
(.branch 1582 30576
.empty
.empty)
(.branch 1584 47648
.empty
.empty)))
(.branch 1590 25318
(.branch 1588 48623
(.branch 1587 30630
(.branch 1586 30569
.empty
.empty)
.empty)
(.branch 1589 48672
.empty
.empty))
(.branch 1592 48964
(.branch 1591 25257
.empty
.empty)
(.branch 1593 48971
.empty
.empty))))
(.branch 1603 32041
(.branch 1599 32048
(.branch 1597 47940
(.branch 1596 47947
(.branch 1595 27039
.empty
.empty)
.empty)
(.branch 1598 32095
.empty
.empty))
(.branch 1601 47968
(.branch 1600 47919
.empty
.empty)
(.branch 1602 32102
.empty
.empty)))
(.branch 1608 48940
(.branch 1606 26985
(.branch 1605 48943
(.branch 1604 48992
.empty
.empty)
.empty)
(.branch 1607 27046
.empty
.empty))
(.branch 1610 26998
(.branch 1609 48995
.empty
.empty)
(.branch 1611 27033
.empty
.empty)))))
(.branch 1630 30582
(.branch 1621 48967
(.branch 1617 47944
(.branch 1615 32054
(.branch 1614 32089
(.branch 1613 47916
.empty
.empty)
.empty)
(.branch 1616 47943
.empty
.empty))
(.branch 1619 32047
(.branch 1618 32096
.empty
.empty)
(.branch 1620 48968
.empty
.empty)))
(.branch 1626 25305
(.branch 1624 48675
(.branch 1623 27040
(.branch 1622 26991
.empty
.empty)
.empty)
(.branch 1625 48620
.empty
.empty))
(.branch 1628 47596
(.branch 1627 25270
.empty
.empty)
(.branch 1629 47651
.empty
.empty))))
(.branch 1639 25263
(.branch 1635 30624
(.branch 1633 47623
(.branch 1632 47624
(.branch 1631 30617
.empty
.empty)
.empty)
(.branch 1634 30575
.empty
.empty))
(.branch 1637 48648
(.branch 1636 48647
.empty
.empty)
(.branch 1638 25312
.empty
.empty)))
(.branch 1644 95048
(.branch 1642 86864
(.branch 1641 94998
(.branch 1640 93248
.empty
.empty)
.empty)
(.branch 1643 88998
.empty
.empty))
(.branch 1646 88760
(.branch 1645 92910
.empty
.empty)
(.branch 1647 87006
.empty
.empty))))))
(.branch 1684 93201
(.branch 1666 88711
(.branch 1657 93249
(.branch 1653 93198
(.branch 1651 88710
(.branch 1650 86960
(.branch 1649 95094
.empty
.empty)
.empty)
(.branch 1652 94952
.empty
.empty))
(.branch 1655 86910
(.branch 1654 89048
.empty
.empty)
(.branch 1656 94999
.empty
.empty)))
(.branch 1662 87007
(.branch 1660 92911
(.branch 1659 86865
(.branch 1658 88999
.empty
.empty)
.empty)
(.branch 1661 95049
.empty
.empty))
(.branch 1664 95095
(.branch 1663 88761
.empty
.empty)
(.branch 1665 92961
.empty
.empty))))
(.branch 1675 86863
(.branch 1671 89049
(.branch 1669 94953
(.branch 1668 93199
(.branch 1667 86961
.empty
.empty)
.empty)
(.branch 1670 86911
.empty
.empty))
(.branch 1673 93247
(.branch 1672 95001
.empty
.empty)
(.branch 1674 89001
.empty
.empty)))
(.branch 1680 95097
(.branch 1678 87009
(.branch 1677 95047
(.branch 1676 92913
.empty
.empty)
.empty)
(.branch 1679 88759
.empty
.empty))
(.branch 1682 88713
(.branch 1681 92959
.empty
.empty)
(.branch 1683 86959
.empty
.empty)))))
(.branch 1702 89046
(.branch 1693 92912
(.branch 1689 95000
(.branch 1687 89047
(.branch 1686 86913
(.branch 1685 94951
.empty
.empty)
.empty)
(.branch 1688 93246
.empty
.empty))
(.branch 1691 89000
(.branch 1690 86862
.empty
.empty)
(.branch 1692 95046
.empty
.empty)))
(.branch 1698 86958
(.branch 1696 92958
(.branch 1695 87008
(.branch 1694 88758
.empty
.empty)
.empty)
(.branch 1697 95096
.empty
.empty))
(.branch 1700 94950
(.branch 1699 88712
.empty
.empty)
(.branch 1701 93200
.empty
.empty))))
(.branch 1711 93627
(.branch 1707 88610
(.branch 1705 93578
(.branch 1704 94562
(.branch 1703 86912
.empty
.empty)
.empty)
(.branch 1706 87242
.empty
.empty))
(.branch 1709 88659
(.branch 1708 87291
.empty
.empty)
(.branch 1710 94611
.empty
.empty)))
(.branch 1715 93636
(.branch 1713 88668
(.branch 1712 87300
.empty
.empty)
(.branch 1714 94620
.empty
.empty))
(.branch 1717 93589
(.branch 1716 94573
.empty
.empty)
(.branch 1718 87253
.empty
.empty)))))))))
(.branch 2006 2905
(.branch 1863 30618
(.branch 1791 25630
(.branch 1755 87290
(.branch 1737 94658
(.branch 1728 87348
(.branch 1724 87339
(.branch 1722 87386
(.branch 1721 93338
(.branch 1720 94706
.empty
.empty)
.empty)
(.branch 1723 88370
.empty
.empty))
(.branch 1726 94659
(.branch 1725 88323
.empty
.empty)
(.branch 1727 93291
.empty
.empty)))
(.branch 1733 93349
(.branch 1731 93300
(.branch 1730 94668
(.branch 1729 88332
.empty
.empty)
.empty)
(.branch 1732 94717
.empty
.empty))
(.branch 1735 88381
(.branch 1734 87397
.empty
.empty)
(.branch 1736 93290
.empty
.empty))))
(.branch 1746 93348
(.branch 1742 93339
(.branch 1740 88371
(.branch 1739 87338
(.branch 1738 88322
.empty
.empty)
.empty)
(.branch 1741 87387
.empty
.empty))
(.branch 1744 88380
(.branch 1743 94707
.empty
.empty)
(.branch 1745 87396
.empty
.empty)))
(.branch 1751 87349
(.branch 1749 94669
(.branch 1748 93301
(.branch 1747 94716
.empty
.empty)
.empty)
(.branch 1750 88333
.empty
.empty))
(.branch 1753 94610
(.branch 1752 93626
.empty
.empty)
(.branch 1754 88658
.empty
.empty)))))
(.branch 1773 25622
(.branch 1764 93637
(.branch 1760 88620
(.branch 1758 93579
(.branch 1757 87243
(.branch 1756 88611
.empty
.empty)
.empty)
(.branch 1759 94563
.empty
.empty))
(.branch 1762 93588
(.branch 1761 87252
.empty
.empty)
(.branch 1763 94572
.empty
.empty)))
(.branch 1769 31735
(.branch 1767 87301
(.branch 1766 88669
(.branch 1765 94621
.empty
.empty)
.empty)
(.branch 1768 25591
.empty
.empty))
(.branch 1771 31939
(.branch 1770 25859
.empty
.empty)
(.branch 1772 31766
.empty
.empty))))
(.branch 1782 30946
(.branch 1778 26755
(.branch 1776 26615
(.branch 1775 25890
(.branch 1774 31970
.empty
.empty)
.empty)
(.branch 1777 30839
.empty
.empty))
(.branch 1780 30870
(.branch 1779 30915
.empty
.empty)
(.branch 1781 26646
.empty
.empty)))
(.branch 1787 31743
(.branch 1785 31941
(.branch 1784 25861
(.branch 1783 26786
.empty
.empty)
.empty)
(.branch 1786 25599
.empty
.empty))
(.branch 1789 25892
(.branch 1788 31972
.empty
.empty)
(.branch 1790 31774
.empty
.empty))))))
(.branch 1827 31760
(.branch 1809 31768
(.branch 1800 26648
(.branch 1796 30948
(.branch 1794 26623
(.branch 1793 30917
(.branch 1792 26757
.empty
.empty)
.empty)
(.branch 1795 30847
.empty
.empty))
(.branch 1798 30878
(.branch 1797 26788
.empty
.empty)
(.branch 1799 26654
.empty
.empty)))
(.branch 1805 26617
(.branch 1803 30924
(.branch 1802 26764
(.branch 1801 30872
.empty
.empty)
.empty)
(.branch 1804 30841
.empty
.empty))
(.branch 1807 26733
(.branch 1806 30893
.empty
.empty)
(.branch 1808 25624
.empty
.empty))))
(.branch 1818 26640
(.branch 1814 31917
(.branch 1812 31737
(.branch 1811 31948
(.branch 1810 25868
.empty
.empty)
.empty)
(.branch 1813 25593
.empty
.empty))
(.branch 1816 26762
(.branch 1815 25837
.empty
.empty)
(.branch 1817 30922
.empty
.empty)))
(.branch 1823 26609
(.branch 1821 26731
(.branch 1820 30891
(.branch 1819 30864
.empty
.empty)
.empty)
(.branch 1822 30833
.empty
.empty))
(.branch 1825 31946
(.branch 1824 25866
.empty
.empty)
(.branch 1826 25616
.empty
.empty)))))
(.branch 1845 30581
(.branch 1836 47967
(.branch 1832 47931
(.branch 1830 31729
(.branch 1829 25835
(.branch 1828 31915
.empty
.empty)
.empty)
(.branch 1831 25585
.empty
.empty))
(.branch 1834 48991
(.branch 1833 48671
.empty
.empty)
(.branch 1835 47611
.empty
.empty)))
(.branch 1841 30572
(.branch 1839 47647
(.branch 1838 48955
(.branch 1837 48635
.empty
.empty)
.empty)
(.branch 1840 26997
.empty
.empty))
(.branch 1843 25269
(.branch 1842 32044
.empty
.empty)
(.branch 1844 26988
.empty
.empty))))
(.branch 1854 47920
(.branch 1850 47956
(.branch 1848 48944
(.branch 1847 25260
(.branch 1846 32053
.empty
.empty)
.empty)
(.branch 1849 47636
.empty
.empty))
(.branch 1852 48980
(.branch 1851 48624
.empty
.empty)
(.branch 1853 47600
.empty
.empty)))
(.branch 1859 30627
(.branch 1857 25306
(.branch 1856 32099
(.branch 1855 48660
.empty
.empty)
.empty)
(.branch 1858 27034
.empty
.empty))
(.branch 1861 25315
(.branch 1860 32090
.empty
.empty)
(.branch 1862 27043
.empty
.empty)))))))
(.branch 1935 579
(.branch 1899 10186
(.branch 1881 48952
(.branch 1872 30570
(.branch 1868 48627
(.branch 1866 47603
(.branch 1865 47923
(.branch 1864 48663
.empty
.empty)
.empty)
(.branch 1867 48983
.empty
.empty))
(.branch 1870 47639
(.branch 1869 47959
.empty
.empty)
(.branch 1871 48947
.empty
.empty)))
(.branch 1877 26986
(.branch 1875 32042
(.branch 1874 25267
(.branch 1873 26995
.empty
.empty)
.empty)
(.branch 1876 30579
.empty
.empty))
(.branch 1879 32051
(.branch 1878 25258
.empty
.empty)
(.branch 1880 47644
.empty
.empty))))
(.branch 1890 30629
(.branch 1886 48668
(.branch 1884 47608
(.branch 1883 47964
(.branch 1882 48632
.empty
.empty)
.empty)
(.branch 1885 48988
.empty
.empty))
(.branch 1888 25308
(.branch 1887 47928
.empty
.empty)
(.branch 1889 32101
.empty
.empty)))
(.branch 1895 27045
(.branch 1893 32092
(.branch 1892 25317
(.branch 1891 27036
.empty
.empty)
.empty)
(.branch 1894 30620
.empty
.empty))
(.branch 1897 32988
(.branch 1896 34628
.empty
.empty)
(.branch 1898 592
.empty
.empty)))))
(.branch 1917 34671
(.branch 1908 33231
(.branch 1904 34716
(.branch 1902 10185
(.branch 1901 34635
(.branch 1900 32992
.empty
.empty)
.empty)
(.branch 1903 576
.empty
.empty))
(.branch 1906 1098
(.branch 1905 33235
.empty
.empty)
(.branch 1907 10354
.empty
.empty)))
(.branch 1913 33219
(.branch 1911 1082
(.branch 1910 10353
(.branch 1909 34675
.empty
.empty)
.empty)
(.branch 1912 34720
.empty
.empty))
(.branch 1915 10350
(.branch 1914 1097
.empty
.empty)
(.branch 1916 33215
.empty
.empty))))
(.branch 1926 10169
(.branch 1922 588
(.branch 1920 34644
(.branch 1919 1081
(.branch 1918 10349
.empty
.empty)
.empty)
(.branch 1921 32947
.empty
.empty))
(.branch 1924 32943
(.branch 1923 10170
.empty
.empty)
(.branch 1925 34619
.empty
.empty)))
(.branch 1931 10198
(.branch 1929 32940
(.branch 1928 34616
(.branch 1927 572
.empty
.empty)
.empty)
(.branch 1930 595
.empty
.empty))
(.branch 1933 34647
(.branch 1932 32944
.empty
.empty)
(.branch 1934 10197
.empty
.empty))))))
(.branch 1971 10127
(.branch 1953 32995
(.branch 1944 34672
(.branch 1940 33216
(.branch 1938 1110
(.branch 1937 33212
(.branch 1936 34668
.empty
.empty)
.empty)
(.branch 1939 10402
.empty
.empty))
(.branch 1942 10401
(.branch 1941 34723
.empty
.empty)
(.branch 1943 1094
.empty
.empty)))
(.branch 1949 34719
(.branch 1947 10398
(.branch 1946 1109
(.branch 1945 33228
.empty
.empty)
.empty)
(.branch 1948 33232
.empty
.empty))
(.branch 1951 1093
(.branch 1950 10397
.empty
.empty)
(.branch 1952 34632
.empty
.empty))))
(.branch 1962 9279
(.branch 1958 10181
(.branch 1956 32991
(.branch 1955 10182
(.branch 1954 591
.empty
.empty)
.empty)
(.branch 1957 34631
.empty
.empty))
(.branch 1960 9263
(.branch 1959 575
.empty
.empty)
(.branch 1961 9919
.empty
.empty)))
(.branch 1967 3013
(.branch 1965 2997
(.branch 1964 1285
(.branch 1963 9903
.empty
.empty)
.empty)
(.branch 1966 1269
.empty
.empty))
(.branch 1969 10095
(.branch 1968 9231
.empty
.empty)
(.branch 1970 9248
.empty
.empty)))))
(.branch 1989 3002
(.branch 1980 1674
(.branch 1976 9247
(.branch 1974 1685
(.branch 1973 2901
(.branch 1972 1653
.empty
.empty)
.empty)
(.branch 1975 2906
.empty
.empty))
(.branch 1978 9232
(.branch 1977 10128
.empty
.empty)
(.branch 1979 10096
.empty
.empty)))
(.branch 1985 9904
(.branch 1983 2890
(.branch 1982 1642
(.branch 1981 2917
.empty
.empty)
.empty)
(.branch 1984 9280
.empty
.empty))
(.branch 1987 9920
(.branch 1986 9264
.empty
.empty)
(.branch 1988 1258
.empty
.empty))))
(.branch 1998 3014
(.branch 1994 9907
(.branch 1992 9923
(.branch 1991 2986
(.branch 1990 1274
.empty
.empty)
.empty)
(.branch 1993 9267
.empty
.empty))
(.branch 1996 2998
(.branch 1995 9283
.empty
.empty)
(.branch 1997 1286
.empty
.empty)))
(.branch 2002 10131
(.branch 2000 10099
(.branch 1999 1270
.empty
.empty)
(.branch 2001 9235
.empty
.empty))
(.branch 2004 2902
(.branch 2003 9244
.empty
.empty)
(.branch 2005 1654
.empty
.empty))))))))
(.branch 2149 53215
(.branch 2078 59835
(.branch 2042 54828
(.branch 2024 60876
(.branch 2015 1641
(.branch 2011 9228
(.branch 2009 9251
(.branch 2008 10124
(.branch 2007 1686
.empty
.empty)
.empty)
(.branch 2010 10092
.empty
.empty))
(.branch 2013 1673
(.branch 2012 2918
.empty
.empty)
(.branch 2014 2889
.empty
.empty)))
(.branch 2020 3001
(.branch 2018 9916
(.branch 2017 9276
(.branch 2016 9900
.empty
.empty)
.empty)
(.branch 2019 9260
.empty
.empty))
(.branch 2022 2985
(.branch 2021 1257
.empty
.empty)
(.branch 2023 1273
.empty
.empty))))
(.branch 2033 53450
(.branch 2029 60877
(.branch 2027 60914
(.branch 2026 54540
(.branch 2025 54578
.empty
.empty)
.empty)
(.branch 2028 54579
.empty
.empty))
(.branch 2031 54541
(.branch 2030 60915
.empty
.empty)
(.branch 2032 59844
.empty
.empty)))
(.branch 2038 59787
(.branch 2036 53451
(.branch 2035 59786
(.branch 2034 53508
.empty
.empty)
.empty)
(.branch 2037 59845
.empty
.empty))
(.branch 2040 60780
(.branch 2039 53509
.empty
.empty)
(.branch 2041 54866
.empty
.empty)))))
(.branch 2060 53595
(.branch 2051 59498
(.branch 2047 54829
(.branch 2045 60781
(.branch 2044 54867
(.branch 2043 60818
.empty
.empty)
.empty)
(.branch 2046 60819
.empty
.empty))
(.branch 2049 53546
(.branch 2048 59556
.empty
.empty)
(.branch 2050 53604
.empty
.empty)))
(.branch 2056 59508
(.branch 2054 59499
(.branch 2053 59557
(.branch 2052 53547
.empty
.empty)
.empty)
(.branch 2055 53605
.empty
.empty))
(.branch 2058 53556
(.branch 2057 53594
.empty
.empty)
(.branch 2059 59546
.empty
.empty))))
(.branch 2069 60829
(.branch 2065 54818
(.branch 2063 53557
(.branch 2062 59547
(.branch 2061 59509
.empty
.empty)
.empty)
(.branch 2064 60828
.empty
.empty))
(.branch 2067 60770
(.branch 2066 54876
.empty
.empty)
(.branch 2068 54819
.empty
.empty)))
(.branch 2074 53460
(.branch 2072 59796
(.branch 2071 54877
(.branch 2070 60771
.empty
.empty)
.empty)
(.branch 2073 53498
.empty
.empty))
(.branch 2076 53499
(.branch 2075 59834
.empty
.empty)
(.branch 2077 59797
.empty
.empty))))))
(.branch 2114 59120
(.branch 2096 61208
(.branch 2087 54589
(.branch 2083 60866
(.branch 2081 54530
(.branch 2080 60924
(.branch 2079 53461
.empty
.empty)
.empty)
(.branch 2082 54588
.empty
.empty))
(.branch 2085 60925
(.branch 2084 54531
.empty
.empty)
(.branch 2086 60867
.empty
.empty)))
(.branch 2092 54920
(.branch 2090 61304
(.branch 2089 59169
(.branch 2088 59167
.empty
.empty)
.empty)
(.branch 2091 61302
.empty
.empty))
(.branch 2094 53167
(.branch 2093 54918
.empty
.empty)
(.branch 2095 53169
.empty
.empty))))
(.branch 2105 59406
(.branch 2101 53073
(.branch 2099 59457
(.branch 2098 59455
(.branch 2097 61206
.empty
.empty)
.empty)
(.branch 2100 53071
.empty
.empty))
(.branch 2103 55206
(.branch 2102 55208
.empty
.empty)
(.branch 2104 59408
.empty
.empty)))
(.branch 2110 53120
(.branch 2108 55255
(.branch 2107 61161
(.branch 2106 61159
.empty
.empty)
.empty)
(.branch 2109 55257
.empty
.empty))
(.branch 2112 61255
(.branch 2111 53118
.empty
.empty)
(.branch 2113 61257
.empty
.empty)))))
(.branch 2132 53070
(.branch 2123 61303
(.branch 2119 54969
(.branch 2117 53214
(.branch 2116 53216
(.branch 2115 59118
.empty
.empty)
.empty)
(.branch 2118 54967
.empty
.empty))
(.branch 2121 59168
(.branch 2120 59166
.empty
.empty)
(.branch 2122 61305
.empty
.empty)))
(.branch 2128 61209
(.branch 2126 53166
(.branch 2125 54919
(.branch 2124 54921
.empty
.empty)
.empty)
(.branch 2127 53168
.empty
.empty))
(.branch 2130 59454
(.branch 2129 61207
.empty
.empty)
(.branch 2131 59456
.empty
.empty))))
(.branch 2141 55256
(.branch 2137 59407
(.branch 2135 55207
(.branch 2134 55209
(.branch 2133 53072
.empty
.empty)
.empty)
(.branch 2136 59409
.empty
.empty))
(.branch 2139 61160
(.branch 2138 61158
.empty
.empty)
(.branch 2140 55254
.empty
.empty)))
(.branch 2145 61256
(.branch 2143 53119
(.branch 2142 53121
.empty
.empty)
(.branch 2144 61254
.empty
.empty))
(.branch 2147 59119
(.branch 2146 59121
.empty
.empty)
(.branch 2148 53217
.empty
.empty)))))))
(.branch 2221 30520
(.branch 2185 48884
(.branch 2167 30818
(.branch 2158 25698
(.branch 2154 31709
(.branch 2152 47668
(.branch 2151 54968
(.branch 2150 54966
.empty
.empty)
.empty)
(.branch 2153 48892
.empty
.empty))
(.branch 2156 48920
(.branch 2155 25691
.empty
.empty)
(.branch 2157 47696
.empty
.empty)))
(.branch 2163 26717
(.branch 2161 48692
(.branch 2160 47868
(.branch 2159 31716
.empty
.empty)
.empty)
(.branch 2162 30811
.empty
.empty))
(.branch 2165 47896
(.branch 2164 48720
.empty
.empty)
(.branch 2166 26724
.empty
.empty))))
(.branch 2176 47707
(.branch 2172 48703
(.branch 2170 30772
(.branch 2169 48731
(.branch 2168 47891
.empty
.empty)
.empty)
(.branch 2171 26674
.empty
.empty))
(.branch 2174 26667
(.branch 2173 47863
.empty
.empty)
(.branch 2175 30765
.empty
.empty)))
(.branch 2181 47679
(.branch 2179 25652
(.branch 2178 31666
(.branch 2177 48915
.empty
.empty)
.empty)
(.branch 2180 48887
.empty
.empty))
(.branch 2183 31659
(.branch 2182 25645
.empty
.empty)
(.branch 2184 47676
.empty
.empty)))))
(.branch 2203 26676
(.branch 2194 30813
(.branch 2190 25700
(.branch 2188 48912
(.branch 2187 25693
(.branch 2186 31707
.empty
.empty)
.empty)
(.branch 2189 47704
.empty
.empty))
(.branch 2192 47860
(.branch 2191 31714
.empty
.empty)
(.branch 2193 48700
.empty
.empty)))
(.branch 2199 30820
(.branch 2197 47888
(.branch 2196 48728
(.branch 2195 26715
.empty
.empty)
.empty)
(.branch 2198 26722
.empty
.empty))
(.branch 2201 48723
(.branch 2200 47899
.empty
.empty)
(.branch 2202 30770
.empty
.empty))))
(.branch 2212 48895
(.branch 2208 47699
(.branch 2206 26669
(.branch 2205 47871
(.branch 2204 48695
.empty
.empty)
.empty)
(.branch 2207 30763
.empty
.empty))
(.branch 2210 31668
(.branch 2209 48923
.empty
.empty)
(.branch 2211 25650
.empty
.empty)))
(.branch 2217 25367
(.branch 2215 31661
(.branch 2214 25643
(.branch 2213 47671
.empty
.empty)
.empty)
(.branch 2216 27064
.empty
.empty))
(.branch 2219 25336
(.branch 2218 27095
.empty
.empty)
(.branch 2220 32023
.empty
.empty))))))
(.branch 2257 25547
(.branch 2239 32234
(.branch 2230 30499
(.branch 2226 25516
(.branch 2224 25571
(.branch 2223 30551
(.branch 2222 31992
.empty
.empty)
.empty)
(.branch 2225 26924
.empty
.empty))
(.branch 2228 30444
(.branch 2227 26979
.empty
.empty)
(.branch 2229 32291
.empty
.empty)))
(.branch 2235 26981
(.branch 2233 26922
(.branch 2232 25573
(.branch 2231 32236
.empty
.empty)
.empty)
(.branch 2234 25514
.empty
.empty))
(.branch 2237 32293
(.branch 2236 30442
.empty
.empty)
(.branch 2238 30501
.empty
.empty))))
(.branch 2248 25361
(.branch 2244 32031
(.branch 2242 27103
(.branch 2241 25375
(.branch 2240 27056
.empty
.empty)
.empty)
(.branch 2243 25328
.empty
.empty))
(.branch 2246 31984
(.branch 2245 30512
.empty
.empty)
(.branch 2247 30559
.empty
.empty)))
(.branch 2253 32017
(.branch 2251 27089
(.branch 2250 25342
(.branch 2249 27070
.empty
.empty)
.empty)
(.branch 2252 30526
.empty
.empty))
(.branch 2255 31998
(.branch 2254 30545
.empty
.empty)
(.branch 2256 26948
.empty
.empty)))))
(.branch 2275 27097
(.branch 2266 26957
(.branch 2262 32260
(.branch 2260 32267
(.branch 2259 25540
(.branch 2258 26955
.empty
.empty)
.empty)
(.branch 2261 30468
.empty
.empty))
(.branch 2264 26946
(.branch 2263 30475
.empty
.empty)
(.branch 2265 25549
.empty
.empty)))
(.branch 2271 30477
(.branch 2269 30466
(.branch 2268 32269
(.branch 2267 25538
.empty
.empty)
.empty)
(.branch 2270 32258
.empty
.empty))
(.branch 2273 27062
(.branch 2272 25369
.empty
.empty)
(.branch 2274 25334
.empty
.empty))))
(.branch 2284 95076
(.branch 2280 88683
(.branch 2278 30553
(.branch 2277 32025
(.branch 2276 30518
.empty
.empty)
.empty)
(.branch 2279 31990
.empty
.empty))
(.branch 2282 95019
(.branch 2281 95066
.empty
.empty)
(.branch 2283 88730
.empty
.empty)))
(.branch 2288 88971
(.branch 2286 88740
(.branch 2285 88693
.empty
.empty)
(.branch 2287 95029
.empty
.empty))
(.branch 2290 94923
(.branch 2289 94970
.empty
.empty)
(.branch 2291 89018
.empty
.empty)))))))))))
(.branch 3438 53496
(.branch 2865 5
(.branch 2579 47613
(.branch 2436 54848
(.branch 2364 93609
(.branch 2328 89019
(.branch 2310 86988
(.branch 2301 86941
(.branch 2297 93218
(.branch 2295 94933
(.branch 2294 89028
(.branch 2293 88981
.empty
.empty)
.empty)
(.branch 2296 86931
.empty
.empty))
(.branch 2299 86882
(.branch 2298 93267
.empty
.empty)
(.branch 2300 93228
.empty
.empty)))
(.branch 2306 92979
(.branch 2304 87027
(.branch 2303 93277
(.branch 2302 86892
.empty
.empty)
.empty)
(.branch 2305 92930
.empty
.empty))
(.branch 2308 92940
(.branch 2307 86978
.empty
.empty)
(.branch 2309 87037
.empty
.empty))))
(.branch 2319 92941
(.branch 2315 87026
(.branch 2313 92978
(.branch 2312 86979
(.branch 2311 92989
.empty
.empty)
.empty)
(.branch 2314 92931
.empty
.empty))
(.branch 2317 86989
(.branch 2316 92988
.empty
.empty)
(.branch 2318 87036
.empty
.empty)))
(.branch 2324 93276
(.branch 2322 93219
(.branch 2321 93266
(.branch 2320 86883
.empty
.empty)
.empty)
(.branch 2323 86930
.empty
.empty))
(.branch 2326 86940
(.branch 2325 86893
.empty
.empty)
(.branch 2327 93229
.empty
.empty)))))
(.branch 2346 88352
(.branch 2337 95018
(.branch 2333 89029
(.branch 2331 88970
(.branch 2330 94971
(.branch 2329 94922
.empty
.empty)
.empty)
(.branch 2332 94932
.empty
.empty))
(.branch 2335 94981
(.branch 2334 88980
.empty
.empty)
(.branch 2336 88731
.empty
.empty)))
(.branch 2342 88692
(.branch 2340 95028
(.branch 2339 88682
(.branch 2338 95067
.empty
.empty)
.empty)
(.branch 2341 88741
.empty
.empty))
(.branch 2344 87417
(.branch 2343 95077
.empty
.empty)
(.branch 2345 87415
.empty
.empty))))
(.branch 2355 88591
(.branch 2351 93319
(.branch 2349 94638
(.branch 2348 94640
(.branch 2347 88350
.empty
.empty)
.empty)
(.branch 2350 93321
.empty
.empty))
(.branch 2353 87270
(.branch 2352 87272
.empty
.empty)
(.branch 2354 88593
.empty
.empty)))
(.branch 2360 88640
(.branch 2358 93656
(.branch 2357 94591
(.branch 2356 94593
.empty
.empty)
.empty)
(.branch 2359 93654
.empty
.empty))
(.branch 2362 87321
(.branch 2361 88638
.empty
.empty)
(.branch 2363 87319
.empty
.empty))))))
(.branch 2400 88302
(.branch 2382 93318
(.branch 2373 93366
(.branch 2369 88303
(.branch 2367 94542
(.branch 2366 94544
(.branch 2365 93607
.empty
.empty)
.empty)
(.branch 2368 88305
.empty
.empty))
(.branch 2371 87366
(.branch 2370 87368
.empty
.empty)
(.branch 2372 93368
.empty
.empty)))
(.branch 2378 88351
(.branch 2376 87414
(.branch 2375 94687
(.branch 2374 94689
.empty
.empty)
.empty)
(.branch 2377 87416
.empty
.empty))
(.branch 2380 94639
(.branch 2379 88353
.empty
.empty)
(.branch 2381 94641
.empty
.empty))))
(.branch 2391 93657
(.branch 2387 88592
(.branch 2385 87273
(.branch 2384 87271
(.branch 2383 93320
.empty
.empty)
.empty)
(.branch 2386 88590
.empty
.empty))
(.branch 2389 94592
(.branch 2388 94590
.empty
.empty)
(.branch 2390 93655
.empty
.empty)))
(.branch 2396 93606
(.branch 2394 87318
(.branch 2393 88641
(.branch 2392 88639
.empty
.empty)
.empty)
(.branch 2395 87320
.empty
.empty))
(.branch 2398 94543
(.branch 2397 93608
.empty
.empty)
(.branch 2399 94545
.empty
.empty)))))
(.branch 2418 59529
(.branch 2409 53574
(.branch 2405 93369
(.branch 2403 87369
(.branch 2402 87367
(.branch 2401 88304
.empty
.empty)
.empty)
(.branch 2404 93367
.empty
.empty))
(.branch 2407 94688
(.branch 2406 94686
.empty
.empty)
(.branch 2408 60750
.empty
.empty)))
(.branch 2414 59527
(.branch 2412 53527
(.branch 2411 59862
(.branch 2410 54558
.empty
.empty)
.empty)
(.branch 2413 60895
.empty
.empty))
(.branch 2416 53529
(.branch 2415 54799
.empty
.empty)
(.branch 2417 60897
.empty
.empty))))
(.branch 2427 53478
(.branch 2423 59864
(.branch 2421 53576
(.branch 2420 60752
(.branch 2419 54801
.empty
.empty)
.empty)
(.branch 2422 54560
.empty
.empty))
(.branch 2425 59574
(.branch 2424 54846
.empty
.empty)
(.branch 2426 60846
.empty
.empty)))
(.branch 2432 59817
(.branch 2430 53623
(.branch 2429 54511
(.branch 2428 59815
.empty
.empty)
.empty)
(.branch 2431 60799
.empty
.empty))
(.branch 2434 53625
(.branch 2433 54513
.empty
.empty)
(.branch 2435 60801
.empty
.empty)))))))
(.branch 2508 54938
(.branch 2472 59485
(.branch 2454 59526
(.branch 2445 53577
(.branch 2441 60896
(.branch 2439 53480
(.branch 2438 60848
(.branch 2437 59576
.empty
.empty)
.empty)
(.branch 2440 53528
.empty
.empty))
(.branch 2443 54800
(.branch 2442 59528
.empty
.empty)
(.branch 2444 60753
.empty
.empty)))
(.branch 2450 54559
(.branch 2448 60751
(.branch 2447 59865
(.branch 2446 54561
.empty
.empty)
.empty)
(.branch 2449 53575
.empty
.empty))
(.branch 2452 53526
(.branch 2451 59863
.empty
.empty)
(.branch 2453 60894
.empty
.empty))))
(.branch 2463 53481
(.branch 2459 60800
(.branch 2457 54512
(.branch 2456 59816
(.branch 2455 54798
.empty
.empty)
.empty)
(.branch 2458 53624
.empty
.empty))
(.branch 2461 59577
(.branch 2460 54849
.empty
.empty)
(.branch 2462 60849
.empty
.empty)))
(.branch 2468 59814
(.branch 2466 60847
(.branch 2465 59575
(.branch 2464 54847
.empty
.empty)
.empty)
(.branch 2467 53479
.empty
.empty))
(.branch 2470 53622
(.branch 2469 54510
.empty
.empty)
(.branch 2471 60798
.empty
.empty)))))
(.branch 2490 53091
(.branch 2481 55237
(.branch 2477 55178
(.branch 2475 61189
(.branch 2474 53100
(.branch 2473 55188
.empty
.empty)
.empty)
(.branch 2476 59475
.empty
.empty))
(.branch 2479 61179
(.branch 2478 53090
.empty
.empty)
(.branch 2480 59436
.empty
.empty)))
(.branch 2486 53139
(.branch 2484 59426
(.branch 2483 61140
(.branch 2482 53149
.empty
.empty)
.empty)
(.branch 2485 55227
.empty
.empty))
(.branch 2488 59474
(.branch 2487 61130
.empty
.empty)
(.branch 2489 55179
.empty
.empty))))
(.branch 2499 61131
(.branch 2495 61188
(.branch 2493 55189
(.branch 2492 59484
(.branch 2491 61178
.empty
.empty)
.empty)
(.branch 2494 53101
.empty
.empty))
(.branch 2497 55226
(.branch 2496 59427
.empty
.empty)
(.branch 2498 53138
.empty
.empty)))
(.branch 2504 54948
(.branch 2502 53148
(.branch 2501 55236
(.branch 2500 59437
.empty
.empty)
.empty)
(.branch 2503 61141
.empty
.empty))
(.branch 2506 61237
(.branch 2505 59149
.empty
.empty)
(.branch 2507 53244
.empty
.empty))))))
(.branch 2544 48950
(.branch 2526 61236
(.branch 2517 59186
(.branch 2513 59196
(.branch 2511 53234
(.branch 2510 61227
(.branch 2509 59139
.empty
.empty)
.empty)
(.branch 2512 54901
.empty
.empty))
(.branch 2515 53197
(.branch 2514 61284
.empty
.empty)
(.branch 2516 54891
.empty
.empty)))
(.branch 2522 61226
(.branch 2520 54939
(.branch 2519 53187
(.branch 2518 61274
.empty
.empty)
.empty)
(.branch 2521 59138
.empty
.empty))
(.branch 2524 54949
(.branch 2523 53235
.empty
.empty)
(.branch 2525 59148
.empty
.empty))))
(.branch 2535 53196
(.branch 2531 53186
(.branch 2529 59187
(.branch 2528 54890
(.branch 2527 53245
.empty
.empty)
.empty)
(.branch 2530 61275
.empty
.empty))
(.branch 2533 59197
(.branch 2532 54900
.empty
.empty)
(.branch 2534 61285
.empty
.empty)))
(.branch 2540 48949
(.branch 2538 27003
(.branch 2537 25275
(.branch 2536 27028
.empty
.empty)
.empty)
(.branch 2539 25300
.empty
.empty))
(.branch 2542 48986
(.branch 2541 48666
.empty
.empty)
(.branch 2543 48629
.empty
.empty)))))
(.branch 2562 47926
(.branch 2553 30612
(.branch 2549 25291
(.branch 2547 48630
(.branch 2546 48985
(.branch 2545 48665
.empty
.empty)
.empty)
(.branch 2548 27012
.empty
.empty))
(.branch 2551 25284
(.branch 2550 27019
.empty
.empty)
(.branch 2552 32059
.empty
.empty)))
(.branch 2558 47925
(.branch 2556 47962
(.branch 2555 30587
(.branch 2554 32084
.empty
.empty)
.empty)
(.branch 2557 47605
.empty
.empty))
(.branch 2560 47961
(.branch 2559 47642
.empty
.empty)
(.branch 2561 47606
.empty
.empty))))
(.branch 2571 30594
(.branch 2567 30603
(.branch 2565 30596
(.branch 2564 32075
(.branch 2563 47641
.empty
.empty)
.empty)
(.branch 2566 32068
.empty
.empty))
(.branch 2569 30605
(.branch 2568 32066
.empty
.empty)
(.branch 2570 32077
.empty
.empty)))
(.branch 2575 47614
(.branch 2573 47633
(.branch 2572 47934
.empty
.empty)
(.branch 2574 47953
.empty
.empty))
(.branch 2577 47634
(.branch 2576 47933
.empty
.empty)
(.branch 2578 47954
.empty
.empty))))))))
(.branch 2722 93576
(.branch 2651 25293
(.branch 2615 25284
(.branch 2597 25298
(.branch 2588 48977
(.branch 2584 27021
(.branch 2582 32061
(.branch 2581 30589
(.branch 2580 32082
.empty
.empty)
.empty)
(.branch 2583 30610
.empty
.empty))
(.branch 2586 27010
(.branch 2585 25282
.empty
.empty)
(.branch 2587 25293
.empty
.empty)))
(.branch 2593 48637
(.branch 2591 48657
(.branch 2590 48958
(.branch 2589 48638
.empty
.empty)
.empty)
(.branch 2592 48978
.empty
.empty))
(.branch 2595 48658
(.branch 2594 48957
.empty
.empty)
(.branch 2596 27005
.empty
.empty))))
(.branch 2606 48986
(.branch 2602 27003
(.branch 2600 27028
(.branch 2599 25277
(.branch 2598 27026
.empty
.empty)
.empty)
(.branch 2601 25275
.empty
.empty))
(.branch 2604 48949
(.branch 2603 25300
.empty
.empty)
(.branch 2605 48666
.empty
.empty)))
(.branch 2611 48630
(.branch 2609 48665
(.branch 2608 48950
(.branch 2607 48629
.empty
.empty)
.empty)
(.branch 2610 48985
.empty
.empty))
(.branch 2613 25291
(.branch 2612 27012
.empty
.empty)
(.branch 2614 27019
.empty
.empty)))))
(.branch 2633 30605
(.branch 2624 47961
(.branch 2620 47962
(.branch 2618 32084
(.branch 2617 30612
(.branch 2616 32059
.empty
.empty)
.empty)
(.branch 2619 30587
.empty
.empty))
(.branch 2622 47925
(.branch 2621 47605
.empty
.empty)
(.branch 2623 47642
.empty
.empty)))
(.branch 2629 30596
(.branch 2627 47641
(.branch 2626 47926
(.branch 2625 47606
.empty
.empty)
.empty)
(.branch 2628 32075
.empty
.empty))
(.branch 2631 30603
(.branch 2630 32068
.empty
.empty)
(.branch 2632 32066
.empty
.empty))))
(.branch 2642 47954
(.branch 2638 47953
(.branch 2636 47934
(.branch 2635 30594
(.branch 2634 32077
.empty
.empty)
.empty)
(.branch 2637 47633
.empty
.empty))
(.branch 2640 47933
(.branch 2639 47614
.empty
.empty)
(.branch 2641 47634
.empty
.empty)))
(.branch 2647 30610
(.branch 2645 30589
(.branch 2644 32082
(.branch 2643 47613
.empty
.empty)
.empty)
(.branch 2646 32061
.empty
.empty))
(.branch 2649 25282
(.branch 2648 27021
.empty
.empty)
(.branch 2650 27010
.empty
.empty))))))
(.branch 2687 93289
(.branch 2669 88609
(.branch 2660 27005
(.branch 2656 48978
(.branch 2654 48958
(.branch 2653 48638
(.branch 2652 48977
.empty
.empty)
.empty)
(.branch 2655 48657
.empty
.empty))
(.branch 2658 48957
(.branch 2657 48637
.empty
.empty)
(.branch 2659 48658
.empty
.empty)))
(.branch 2665 93590
(.branch 2663 25277
(.branch 2662 27026
(.branch 2661 25298
.empty
.empty)
.empty)
(.branch 2664 94574
.empty
.empty))
(.branch 2667 88670
(.branch 2666 87302
.empty
.empty)
(.branch 2668 87241
.empty
.empty))))
(.branch 2678 87303
(.branch 2674 94608
(.branch 2672 87240
(.branch 2671 93625
(.branch 2670 94609
.empty
.empty)
.empty)
(.branch 2673 88608
.empty
.empty))
(.branch 2676 94575
(.branch 2675 93624
.empty
.empty)
(.branch 2677 93591
.empty
.empty)))
(.branch 2683 88334
(.branch 2681 93350
(.branch 2680 94718
(.branch 2679 88671
.empty
.empty)
.empty)
(.branch 2682 87350
.empty
.empty))
(.branch 2685 88369
(.branch 2684 87385
.empty
.empty)
(.branch 2686 94657
.empty
.empty)))))
(.branch 2705 87336
(.branch 2696 93302
(.branch 2692 94719
(.branch 2690 94656
(.branch 2689 88368
(.branch 2688 87384
.empty
.empty)
.empty)
(.branch 2691 93288
.empty
.empty))
(.branch 2694 87351
(.branch 2693 93351
.empty
.empty)
(.branch 2695 88335
.empty
.empty)))
(.branch 2701 87337
(.branch 2699 87398
(.branch 2698 88382
(.branch 2697 94670
.empty
.empty)
.empty)
(.branch 2700 88321
.empty
.empty))
(.branch 2703 94705
(.branch 2702 93337
.empty
.empty)
(.branch 2704 88320
.empty
.empty))))
(.branch 2714 88622
(.branch 2710 88383
(.branch 2708 93303
(.branch 2707 94704
(.branch 2706 93336
.empty
.empty)
.empty)
(.branch 2709 94671
.empty
.empty))
(.branch 2712 93638
(.branch 2711 87399
.empty
.empty)
(.branch 2713 94622
.empty
.empty)))
(.branch 2718 93577
(.branch 2716 88657
(.branch 2715 87254
.empty
.empty)
(.branch 2717 87289
.empty
.empty))
(.branch 2720 88656
(.branch 2719 94561
.empty
.empty)
(.branch 2721 87288
.empty
.empty)))))))
(.branch 2794 437
(.branch 2758 87351
(.branch 2740 94575
(.branch 2731 88670
(.branch 2727 87255
(.branch 2725 94623
(.branch 2724 93639
(.branch 2723 94560
.empty
.empty)
.empty)
(.branch 2726 88623
.empty
.empty))
(.branch 2729 93590
(.branch 2728 94574
.empty
.empty)
(.branch 2730 87302
.empty
.empty)))
(.branch 2736 87240
(.branch 2734 94609
(.branch 2733 88609
(.branch 2732 87241
.empty
.empty)
.empty)
(.branch 2735 93625
.empty
.empty))
(.branch 2738 94608
(.branch 2737 88608
.empty
.empty)
(.branch 2739 93624
.empty
.empty))))
(.branch 2749 88369
(.branch 2745 93350
(.branch 2743 88671
(.branch 2742 87303
(.branch 2741 93591
.empty
.empty)
.empty)
(.branch 2744 94718
.empty
.empty))
(.branch 2747 88334
(.branch 2746 87350
.empty
.empty)
(.branch 2748 87385
.empty
.empty)))
(.branch 2754 94656
(.branch 2752 87384
(.branch 2751 93289
(.branch 2750 94657
.empty
.empty)
.empty)
(.branch 2753 88368
.empty
.empty))
(.branch 2756 94719
(.branch 2755 93288
.empty
.empty)
(.branch 2757 93351
.empty
.empty)))))
(.branch 2776 93638
(.branch 2767 94705
(.branch 2763 87398
(.branch 2761 94670
(.branch 2760 93302
(.branch 2759 88335
.empty
.empty)
.empty)
(.branch 2762 88382
.empty
.empty))
(.branch 2765 87337
(.branch 2764 88321
.empty
.empty)
(.branch 2766 93337
.empty
.empty)))
(.branch 2772 93303
(.branch 2770 93336
(.branch 2769 87336
(.branch 2768 88320
.empty
.empty)
.empty)
(.branch 2771 94704
.empty
.empty))
(.branch 2774 88383
(.branch 2773 94671
.empty
.empty)
(.branch 2775 87399
.empty
.empty))))
(.branch 2785 87288
(.branch 2781 87289
(.branch 2779 87254
(.branch 2778 88622
(.branch 2777 94622
.empty
.empty)
.empty)
(.branch 2780 88657
.empty
.empty))
(.branch 2783 94561
(.branch 2782 93577
.empty
.empty)
(.branch 2784 88656
.empty
.empty)))
(.branch 2790 88623
(.branch 2788 93639
(.branch 2787 94560
(.branch 2786 93576
.empty
.empty)
.empty)
(.branch 2789 94623
.empty
.empty))
(.branch 2792 34564
(.branch 2791 87255
.empty
.empty)
(.branch 2793 34588
.empty
.empty))))))
(.branch 2830 34582
(.branch 2812 28
(.branch 2803 34545
(.branch 2799 34546
(.branch 2797 27
(.branch 2796 29
(.branch 2795 406
.empty
.empty)
.empty)
(.branch 2798 34570
.empty
.empty))
(.branch 2801 5
(.branch 2800 7
.empty
.empty)
(.branch 2802 34569
.empty
.empty)))
(.branch 2808 34592
(.branch 2806 438
(.branch 2805 34547
(.branch 2804 34571
.empty
.empty)
.empty)
(.branch 2807 407
.empty
.empty))
(.branch 2810 422
(.branch 2809 34580
.empty
.empty)
(.branch 2811 451
.empty
.empty))))
(.branch 2821 34555
(.branch 2817 8
(.branch 2815 34554
(.branch 2814 34542
(.branch 2813 30
.empty
.empty)
.empty)
(.branch 2816 6
.empty
.empty))
(.branch 2819 34553
(.branch 2818 34541
.empty
.empty)
(.branch 2820 34543
.empty
.empty)))
(.branch 2826 175
(.branch 2824 34552
(.branch 2823 452
(.branch 2822 423
.empty
.empty)
.empty)
(.branch 2825 34540
.empty
.empty))
(.branch 2828 306
(.branch 2827 146
.empty
.empty)
(.branch 2829 304
.empty
.empty)))))
(.branch 2848 281
(.branch 2839 147
(.branch 2835 34593
(.branch 2833 282
(.branch 2832 284
(.branch 2831 34594
.empty
.empty)
.empty)
(.branch 2834 34581
.empty
.empty))
(.branch 2837 34595
(.branch 2836 34583
.empty
.empty)
(.branch 2838 176
.empty
.empty)))
(.branch 2844 303
(.branch 2842 130
(.branch 2841 34568
(.branch 2840 34544
.empty
.empty)
.empty)
(.branch 2843 161
.empty
.empty))
(.branch 2846 34590
(.branch 2845 305
.empty
.empty)
(.branch 2847 34566
.empty
.empty))))
(.branch 2857 34588
(.branch 2853 34567
(.branch 2851 34565
(.branch 2850 34589
(.branch 2849 283
.empty
.empty)
.empty)
(.branch 2852 34591
.empty
.empty))
(.branch 2855 162
(.branch 2854 131
.empty
.empty)
(.branch 2856 34564
.empty
.empty)))
(.branch 2861 27
(.branch 2859 406
(.branch 2858 437
.empty
.empty)
(.branch 2860 29
.empty
.empty))
(.branch 2863 34546
(.branch 2862 34570
.empty
.empty)
(.branch 2864 7
.empty
.empty)))))))))
(.branch 3152 26691
(.branch 3009 59184
(.branch 2937 59150
(.branch 2901 34595
(.branch 2883 34553
(.branch 2874 422
(.branch 2870 438
(.branch 2868 34571
(.branch 2867 34545
(.branch 2866 34569
.empty
.empty)
.empty)
(.branch 2869 34547
.empty
.empty))
(.branch 2872 34592
(.branch 2871 407
.empty
.empty)
(.branch 2873 34580
.empty
.empty)))
(.branch 2879 34554
(.branch 2877 30
(.branch 2876 28
(.branch 2875 451
.empty
.empty)
.empty)
(.branch 2878 34542
.empty
.empty))
(.branch 2881 8
(.branch 2880 6
.empty
.empty)
(.branch 2882 34541
.empty
.empty))))
(.branch 2892 306
(.branch 2888 34552
(.branch 2886 423
(.branch 2885 34555
(.branch 2884 34543
.empty
.empty)
.empty)
(.branch 2887 452
.empty
.empty))
(.branch 2890 175
(.branch 2889 34540
.empty
.empty)
(.branch 2891 146
.empty
.empty)))
(.branch 2897 282
(.branch 2895 34594
(.branch 2894 34582
(.branch 2893 304
.empty
.empty)
.empty)
(.branch 2896 284
.empty
.empty))
(.branch 2899 34593
(.branch 2898 34581
.empty
.empty)
(.branch 2900 34583
.empty
.empty)))))
(.branch 2919 162
(.branch 2910 34590
(.branch 2906 130
(.branch 2904 34544
(.branch 2903 147
(.branch 2902 176
.empty
.empty)
.empty)
(.branch 2905 34568
.empty
.empty))
(.branch 2908 303
(.branch 2907 161
.empty
.empty)
(.branch 2909 305
.empty
.empty)))
(.branch 2915 34565
(.branch 2913 283
(.branch 2912 281
(.branch 2911 34566
.empty
.empty)
.empty)
(.branch 2914 34589
.empty
.empty))
(.branch 2917 34567
(.branch 2916 34591
.empty
.empty)
(.branch 2918 131
.empty
.empty))))
(.branch 2928 59424
(.branch 2924 59425
(.branch 2922 53102
(.branch 2921 55190
(.branch 2920 59486
.empty
.empty)
.empty)
(.branch 2923 61190
.empty
.empty))
(.branch 2926 53137
(.branch 2925 55225
.empty
.empty)
(.branch 2927 61129
.empty
.empty)))
(.branch 2933 55191
(.branch 2931 61128
(.branch 2930 53136
(.branch 2929 55224
.empty
.empty)
.empty)
(.branch 2932 59487
.empty
.empty))
(.branch 2935 61191
(.branch 2934 53103
.empty
.empty)
(.branch 2936 54950
.empty
.empty))))))
(.branch 2973 53089
(.branch 2955 54902
(.branch 2946 61272
(.branch 2942 61273
(.branch 2940 54889
(.branch 2939 53246
(.branch 2938 61238
.empty
.empty)
.empty)
(.branch 2941 59185
.empty
.empty))
(.branch 2944 54888
(.branch 2943 53185
.empty
.empty)
(.branch 2945 59184
.empty
.empty)))
(.branch 2951 53247
(.branch 2949 59151
(.branch 2948 54951
(.branch 2947 53184
.empty
.empty)
.empty)
(.branch 2950 61239
.empty
.empty))
(.branch 2953 61286
(.branch 2952 53198
.empty
.empty)
(.branch 2954 59198
.empty
.empty))))
(.branch 2964 53199
(.branch 2960 53232
(.branch 2958 59137
(.branch 2957 61225
(.branch 2956 53233
.empty
.empty)
.empty)
(.branch 2959 54937
.empty
.empty))
(.branch 2962 59136
(.branch 2961 61224
.empty
.empty)
(.branch 2963 54936
.empty
.empty)))
(.branch 2969 53150
(.branch 2967 54903
(.branch 2966 59199
(.branch 2965 61287
.empty
.empty)
.empty)
(.branch 2968 61142
.empty
.empty))
(.branch 2971 59438
(.branch 2970 55238
.empty
.empty)
(.branch 2972 61177
.empty
.empty)))))
(.branch 2991 61129
(.branch 2982 55239
(.branch 2978 55176
(.branch 2976 61176
(.branch 2975 59473
(.branch 2974 55177
.empty
.empty)
.empty)
(.branch 2977 53088
.empty
.empty))
(.branch 2980 61143
(.branch 2979 59472
.empty
.empty)
(.branch 2981 53151
.empty
.empty)))
(.branch 2987 61190
(.branch 2985 55190
(.branch 2984 59486
(.branch 2983 59439
.empty
.empty)
.empty)
(.branch 2986 53102
.empty
.empty))
(.branch 2989 55225
(.branch 2988 59425
.empty
.empty)
(.branch 2990 53137
.empty
.empty))))
(.branch 3000 54950
(.branch 2996 59487
(.branch 2994 53136
(.branch 2993 55224
(.branch 2992 59424
.empty
.empty)
.empty)
(.branch 2995 61128
.empty
.empty))
(.branch 2998 53103
(.branch 2997 55191
.empty
.empty)
(.branch 2999 61191
.empty
.empty)))
(.branch 3005 59185
(.branch 3003 53246
(.branch 3002 61238
(.branch 3001 59150
.empty
.empty)
.empty)
(.branch 3004 54889
.empty
.empty))
(.branch 3007 53185
(.branch 3006 61273
.empty
.empty)
(.branch 3008 54888
.empty
.empty)))))))
(.branch 3081 48917
(.branch 3045 53151
(.branch 3027 54936
(.branch 3018 59198
(.branch 3014 61239
(.branch 3012 54951
(.branch 3011 53184
(.branch 3010 61272
.empty
.empty)
.empty)
(.branch 3013 59151
.empty
.empty))
(.branch 3016 53198
(.branch 3015 53247
.empty
.empty)
(.branch 3017 61286
.empty
.empty)))
(.branch 3023 54937
(.branch 3021 61225
(.branch 3020 53233
(.branch 3019 54902
.empty
.empty)
.empty)
(.branch 3022 59137
.empty
.empty))
(.branch 3025 61224
(.branch 3024 53232
.empty
.empty)
(.branch 3026 59136
.empty
.empty))))
(.branch 3036 61177
(.branch 3032 61142
(.branch 3030 59199
(.branch 3029 61287
(.branch 3028 53199
.empty
.empty)
.empty)
(.branch 3031 54903
.empty
.empty))
(.branch 3034 55238
(.branch 3033 53150
.empty
.empty)
(.branch 3035 59438
.empty
.empty)))
(.branch 3041 53088
(.branch 3039 59473
(.branch 3038 55177
(.branch 3037 53089
.empty
.empty)
.empty)
(.branch 3040 61176
.empty
.empty))
(.branch 3043 59472
(.branch 3042 55176
.empty
.empty)
(.branch 3044 61143
.empty
.empty)))))
(.branch 3063 30803
(.branch 3054 47702
(.branch 3050 48926
(.branch 3048 25667
(.branch 3047 59439
(.branch 3046 55239
.empty
.empty)
.empty)
(.branch 3049 48925
.empty
.empty))
(.branch 3052 31685
(.branch 3051 25683
.empty
.empty)
(.branch 3053 47701
.empty
.empty)))
(.branch 3059 26709
(.branch 3057 48725
(.branch 3056 26693
(.branch 3055 31701
.empty
.empty)
.empty)
(.branch 3058 48726
.empty
.empty))
(.branch 3061 47901
(.branch 3060 30787
.empty
.empty)
(.branch 3062 47902
.empty
.empty))))
(.branch 3072 25676
(.branch 3068 30796
(.branch 3066 48697
(.branch 3065 48698
(.branch 3064 26698
.empty
.empty)
.empty)
(.branch 3067 26682
.empty
.empty))
(.branch 3070 47857
(.branch 3069 47858
.empty
.empty)
(.branch 3071 30780
.empty
.empty)))
(.branch 3077 47674
(.branch 3075 25660
(.branch 3074 48881
(.branch 3073 48882
.empty
.empty)
.empty)
(.branch 3076 31690
.empty
.empty))
(.branch 3079 31674
(.branch 3078 47673
.empty
.empty)
(.branch 3080 25669
.empty
.empty))))))
(.branch 3117 47701
(.branch 3099 26684
(.branch 3090 48734
(.branch 3086 47710
(.branch 3084 31683
(.branch 3083 25685
(.branch 3082 48918
.empty
.empty)
.empty)
(.branch 3085 47709
.empty
.empty))
(.branch 3088 26691
(.branch 3087 31699
.empty
.empty)
(.branch 3089 48733
.empty
.empty)))
(.branch 3095 30805
(.branch 3093 47893
(.branch 3092 30789
(.branch 3091 26707
.empty
.empty)
.empty)
(.branch 3094 47894
.empty
.empty))
(.branch 3097 48690
(.branch 3096 26700
.empty
.empty)
(.branch 3098 48689
.empty
.empty))))
(.branch 3108 31692
(.branch 3104 25674
(.branch 3102 47865
(.branch 3101 47866
(.branch 3100 30794
.empty
.empty)
.empty)
(.branch 3103 30778
.empty
.empty))
(.branch 3106 48889
(.branch 3105 48890
.empty
.empty)
(.branch 3107 25658
.empty
.empty)))
(.branch 3113 48925
(.branch 3111 31676
(.branch 3110 47665
(.branch 3109 47666
.empty
.empty)
.empty)
(.branch 3112 25667
.empty
.empty))
(.branch 3115 25683
(.branch 3114 48926
.empty
.empty)
(.branch 3116 31685
.empty
.empty)))))
(.branch 3135 30780
(.branch 3126 47902
(.branch 3122 48726
(.branch 3120 26693
(.branch 3119 31701
(.branch 3118 47702
.empty
.empty)
.empty)
(.branch 3121 48725
.empty
.empty))
(.branch 3124 30787
(.branch 3123 26709
.empty
.empty)
(.branch 3125 47901
.empty
.empty)))
(.branch 3131 26682
(.branch 3129 48698
(.branch 3128 26698
(.branch 3127 30803
.empty
.empty)
.empty)
(.branch 3130 48697
.empty
.empty))
(.branch 3133 47858
(.branch 3132 30796
.empty
.empty)
(.branch 3134 47857
.empty
.empty))))
(.branch 3144 25669
(.branch 3140 31690
(.branch 3138 48881
(.branch 3137 48882
(.branch 3136 25676
.empty
.empty)
.empty)
(.branch 3139 25660
.empty
.empty))
(.branch 3142 47673
(.branch 3141 47674
.empty
.empty)
(.branch 3143 31674
.empty
.empty)))
(.branch 3148 31683
(.branch 3146 48918
(.branch 3145 48917
.empty
.empty)
(.branch 3147 25685
.empty
.empty))
(.branch 3150 47710
(.branch 3149 47709
.empty
.empty)
(.branch 3151 31699
.empty
.empty))))))))
(.branch 3295 94680
(.branch 3224 94599
(.branch 3188 87422
(.branch 3170 48889
(.branch 3161 48690
(.branch 3157 47893
(.branch 3155 26707
(.branch 3154 48734
(.branch 3153 48733
.empty
.empty)
.empty)
(.branch 3156 30789
.empty
.empty))
(.branch 3159 30805
(.branch 3158 47894
.empty
.empty)
(.branch 3160 26700
.empty
.empty)))
(.branch 3166 47865
(.branch 3164 30794
(.branch 3163 26684
(.branch 3162 48689
.empty
.empty)
.empty)
(.branch 3165 47866
.empty
.empty))
(.branch 3168 25674
(.branch 3167 30778
.empty
.empty)
(.branch 3169 48890
.empty
.empty))))
(.branch 3179 93374
(.branch 3175 31676
(.branch 3173 47666
(.branch 3172 31692
(.branch 3171 25658
.empty
.empty)
.empty)
(.branch 3174 47665
.empty
.empty))
(.branch 3177 87327
(.branch 3176 87423
.empty
.empty)
(.branch 3178 93662
.empty
.empty)))
(.branch 3184 93648
(.branch 3182 87408
(.branch 3181 93361
(.branch 3180 93649
.empty
.empty)
.empty)
(.branch 3183 87312
.empty
.empty))
(.branch 3186 87409
(.branch 3185 93360
.empty
.empty)
(.branch 3187 87313
.empty
.empty)))))
(.branch 3206 87375
(.branch 3197 87265
(.branch 3193 93327
(.branch 3191 93375
(.branch 3190 93663
(.branch 3189 87326
.empty
.empty)
.empty)
(.branch 3192 93615
.empty
.empty))
(.branch 3195 87278
(.branch 3194 87374
.empty
.empty)
(.branch 3196 87361
.empty
.empty)))
(.branch 3202 93601
(.branch 3200 87360
(.branch 3199 93312
(.branch 3198 93600
.empty
.empty)
.empty)
(.branch 3201 87264
.empty
.empty))
(.branch 3204 93614
(.branch 3203 93313
.empty
.empty)
(.branch 3205 93326
.empty
.empty))))
(.branch 3215 88584
(.branch 3211 94646
(.branch 3209 88599
(.branch 3208 88311
(.branch 3207 87279
.empty
.empty)
.empty)
(.branch 3210 94550
.empty
.empty))
(.branch 3213 94633
(.branch 3212 94537
.empty
.empty)
(.branch 3214 88296
.empty
.empty)))
(.branch 3220 88310
(.branch 3218 88297
(.branch 3217 94632
(.branch 3216 94536
.empty
.empty)
.empty)
(.branch 3219 88585
.empty
.empty))
(.branch 3222 94551
(.branch 3221 88598
.empty
.empty)
(.branch 3223 94647
.empty
.empty))))))
(.branch 3260 87361
(.branch 3242 93662
(.branch 3233 88632
(.branch 3229 88633
(.branch 3227 88646
(.branch 3226 88358
(.branch 3225 94695
.empty
.empty)
.empty)
(.branch 3228 88345
.empty
.empty))
(.branch 3231 94680
(.branch 3230 94584
.empty
.empty)
(.branch 3232 88344
.empty
.empty)))
(.branch 3238 88359
(.branch 3236 94598
(.branch 3235 94681
(.branch 3234 94585
.empty
.empty)
.empty)
(.branch 3237 94694
.empty
.empty))
(.branch 3240 87423
(.branch 3239 88647
.empty
.empty)
(.branch 3241 87327
.empty
.empty))))
(.branch 3251 87313
(.branch 3247 87312
(.branch 3245 93361
(.branch 3244 93649
(.branch 3243 93374
.empty
.empty)
.empty)
(.branch 3246 87408
.empty
.empty))
(.branch 3249 93360
(.branch 3248 93648
.empty
.empty)
(.branch 3250 87409
.empty
.empty)))
(.branch 3256 93615
(.branch 3254 93663
(.branch 3253 87326
(.branch 3252 87422
.empty
.empty)
.empty)
(.branch 3255 93375
.empty
.empty))
(.branch 3258 87374
(.branch 3257 93327
.empty
.empty)
(.branch 3259 87278
.empty
.empty)))))
(.branch 3278 88296
(.branch 3269 93326
(.branch 3265 87264
(.branch 3263 93312
(.branch 3262 93600
(.branch 3261 87265
.empty
.empty)
.empty)
(.branch 3264 87360
.empty
.empty))
(.branch 3267 93313
(.branch 3266 93601
.empty
.empty)
(.branch 3268 93614
.empty
.empty)))
(.branch 3274 94550
(.branch 3272 88311
(.branch 3271 87279
(.branch 3270 87375
.empty
.empty)
.empty)
(.branch 3273 88599
.empty
.empty))
(.branch 3276 94537
(.branch 3275 94646
.empty
.empty)
(.branch 3277 94633
.empty
.empty))))
(.branch 3287 94647
(.branch 3283 88585
(.branch 3281 94632
(.branch 3280 94536
(.branch 3279 88584
.empty
.empty)
.empty)
(.branch 3282 88297
.empty
.empty))
(.branch 3285 88598
(.branch 3284 88310
.empty
.empty)
(.branch 3286 94551
.empty
.empty)))
(.branch 3291 88646
(.branch 3289 94695
(.branch 3288 94599
.empty
.empty)
(.branch 3290 88358
.empty
.empty))
(.branch 3293 88633
(.branch 3292 88345
.empty
.empty)
(.branch 3294 94584
.empty
.empty)))))))
(.branch 3367 1090
(.branch 3331 34641
(.branch 3313 34622
(.branch 3304 573
(.branch 3300 94598
(.branch 3298 94585
(.branch 3297 88632
(.branch 3296 88344
.empty
.empty)
.empty)
(.branch 3299 94681
.empty
.empty))
(.branch 3302 88359
(.branch 3301 94694
.empty
.empty)
(.branch 3303 88647
.empty
.empty)))
(.branch 3309 34621
(.branch 3307 10173
(.branch 3306 10369
(.branch 3305 1086
.empty
.empty)
.empty)
(.branch 3308 34689
.empty
.empty))
(.branch 3311 33229
(.branch 3310 32957
.empty
.empty)
(.branch 3312 34690
.empty
.empty))))
(.branch 3322 589
(.branch 3318 10382
(.branch 3316 594
(.branch 3315 33230
(.branch 3314 32958
.empty
.empty)
.empty)
(.branch 3317 1105
.empty
.empty))
(.branch 3320 10370
(.branch 3319 10194
.empty
.empty)
(.branch 3321 10174
.empty
.empty)))
(.branch 3327 34642
(.branch 3325 33233
(.branch 3324 32961
(.branch 3323 1102
.empty
.empty)
.empty)
(.branch 3326 34702
.empty
.empty))
(.branch 3329 33234
(.branch 3328 32962
.empty
.empty)
(.branch 3330 34701
.empty
.empty)))))
(.branch 3349 1106
(.branch 3340 34685
(.branch 3336 577
(.branch 3334 578
(.branch 3333 10193
(.branch 3332 10381
.empty
.empty)
.empty)
(.branch 3335 1089
.empty
.empty))
(.branch 3338 10365
(.branch 3337 1085
.empty
.empty)
(.branch 3339 10189
.empty
.empty)))
(.branch 3345 34638
(.branch 3343 33213
(.branch 3342 32978
(.branch 3341 34637
.empty
.empty)
.empty)
(.branch 3344 34686
.empty
.empty))
(.branch 3347 33214
(.branch 3346 32977
.empty
.empty)
(.branch 3348 590
.empty
.empty))))
(.branch 3358 34706
(.branch 3354 593
(.branch 3352 10366
(.branch 3351 10178
(.branch 3350 10386
.empty
.empty)
.empty)
(.branch 3353 10190
.empty
.empty))
(.branch 3356 32974
(.branch 3355 1101
.empty
.empty)
(.branch 3357 33217
.empty
.empty)))
(.branch 3363 34625
(.branch 3361 33218
(.branch 3360 32973
(.branch 3359 34626
.empty
.empty)
.empty)
(.branch 3362 34705
.empty
.empty))
(.branch 3365 10177
(.branch 3364 10385
.empty
.empty)
(.branch 3366 574
.empty
.empty))))))
(.branch 3403 10189
(.branch 3385 10174
(.branch 3376 34690
(.branch 3372 34689
(.branch 3370 10369
(.branch 3369 1086
(.branch 3368 573
.empty
.empty)
.empty)
(.branch 3371 10173
.empty
.empty))
(.branch 3374 32957
(.branch 3373 34621
.empty
.empty)
(.branch 3375 33229
.empty
.empty)))
(.branch 3381 1105
(.branch 3379 33230
(.branch 3378 32958
(.branch 3377 34622
.empty
.empty)
.empty)
(.branch 3380 594
.empty
.empty))
(.branch 3383 10194
(.branch 3382 10382
.empty
.empty)
(.branch 3384 10370
.empty
.empty))))
(.branch 3394 34701
(.branch 3390 34702
(.branch 3388 32961
(.branch 3387 1102
(.branch 3386 589
.empty
.empty)
.empty)
(.branch 3389 33233
.empty
.empty))
(.branch 3392 32962
(.branch 3391 34642
.empty
.empty)
(.branch 3393 33234
.empty
.empty)))
(.branch 3399 1089
(.branch 3397 10193
(.branch 3396 10381
(.branch 3395 34641
.empty
.empty)
.empty)
(.branch 3398 578
.empty
.empty))
(.branch 3401 1085
(.branch 3400 577
.empty
.empty)
(.branch 3402 10365
.empty
.empty)))))
(.branch 3421 33217
(.branch 3412 590
(.branch 3408 34686
(.branch 3406 32978
(.branch 3405 34637
(.branch 3404 34685
.empty
.empty)
.empty)
(.branch 3407 33213
.empty
.empty))
(.branch 3410 32977
(.branch 3409 34638
.empty
.empty)
(.branch 3411 33214
.empty
.empty)))
(.branch 3417 10190
(.branch 3415 10178
(.branch 3414 10386
(.branch 3413 1106
.empty
.empty)
.empty)
(.branch 3416 10366
.empty
.empty))
(.branch 3419 1101
(.branch 3418 593
.empty
.empty)
(.branch 3420 32974
.empty
.empty))))
(.branch 3430 574
(.branch 3426 34705
(.branch 3424 32973
(.branch 3423 34626
(.branch 3422 34706
.empty
.empty)
.empty)
(.branch 3425 33218
.empty
.empty))
(.branch 3428 10385
(.branch 3427 34625
.empty
.empty)
(.branch 3429 10177
.empty
.empty)))
(.branch 3434 54528
(.branch 3432 60878
(.branch 3431 1090
.empty
.empty)
(.branch 3433 54529
.empty
.empty))
(.branch 3436 59846
(.branch 3435 60879
.empty
.empty)
(.branch 3437 53497
.empty
.empty))))))))))
(.branch 4011 88695
(.branch 3725 54913
(.branch 3582 32937
(.branch 3510 59784
(.branch 3474 59544
(.branch 3456 54878
(.branch 3447 53463
(.branch 3443 54591
(.branch 3441 60913
(.branch 3440 54590
(.branch 3439 59847
.empty
.empty)
.empty)
(.branch 3442 60912
.empty
.empty))
(.branch 3445 59785
(.branch 3444 53462
.empty
.empty)
(.branch 3446 59784
.empty
.empty)))
(.branch 3452 59558
(.branch 3450 54816
(.branch 3449 54817
(.branch 3448 60782
.empty
.empty)
.empty)
(.branch 3451 60783
.empty
.empty))
(.branch 3454 53592
(.branch 3453 53593
.empty
.empty)
(.branch 3455 59559
.empty
.empty))))
(.branch 3465 53545
(.branch 3461 59497
(.branch 3459 54879
(.branch 3458 60816
(.branch 3457 60817
.empty
.empty)
.empty)
(.branch 3460 53558
.empty
.empty))
(.branch 3463 53559
(.branch 3462 59496
.empty
.empty)
(.branch 3464 59510
.empty
.empty)))
(.branch 3470 54864
(.branch 3468 60830
(.branch 3467 59511
(.branch 3466 53544
.empty
.empty)
.empty)
(.branch 3469 54865
.empty
.empty))
(.branch 3472 53606
(.branch 3471 60831
.empty
.empty)
(.branch 3473 59545
.empty
.empty)))))
(.branch 3492 54542
(.branch 3483 59799
(.branch 3479 54831
(.branch 3477 60769
(.branch 3476 54830
(.branch 3475 53607
.empty
.empty)
.empty)
(.branch 3478 60768
.empty
.empty))
(.branch 3481 53449
(.branch 3480 59798
.empty
.empty)
(.branch 3482 53448
.empty
.empty)))
(.branch 3488 53510
(.branch 3486 54576
(.branch 3485 54577
(.branch 3484 60926
.empty
.empty)
.empty)
(.branch 3487 60927
.empty
.empty))
(.branch 3490 59832
(.branch 3489 59833
.empty
.empty)
(.branch 3491 53511
.empty
.empty))))
(.branch 3501 53497
(.branch 3497 54529
(.branch 3495 54543
(.branch 3494 60864
(.branch 3493 60865
.empty
.empty)
.empty)
(.branch 3496 60878
.empty
.empty))
(.branch 3499 60879
(.branch 3498 54528
.empty
.empty)
(.branch 3500 59846
.empty
.empty)))
(.branch 3506 60912
(.branch 3504 54590
(.branch 3503 59847
(.branch 3502 53496
.empty
.empty)
.empty)
(.branch 3505 60913
.empty
.empty))
(.branch 3508 53462
(.branch 3507 54591
.empty
.empty)
(.branch 3509 59785
.empty
.empty))))))
(.branch 3546 53448
(.branch 3528 59510
(.branch 3519 59559
(.branch 3515 60783
(.branch 3513 54817
(.branch 3512 60782
(.branch 3511 53463
.empty
.empty)
.empty)
(.branch 3514 54816
.empty
.empty))
(.branch 3517 53593
(.branch 3516 59558
.empty
.empty)
(.branch 3518 53592
.empty
.empty)))
(.branch 3524 53558
(.branch 3522 60816
(.branch 3521 60817
(.branch 3520 54878
.empty
.empty)
.empty)
(.branch 3523 54879
.empty
.empty))
(.branch 3526 59496
(.branch 3525 59497
.empty
.empty)
(.branch 3527 53559
.empty
.empty))))
(.branch 3537 59545
(.branch 3533 54865
(.branch 3531 59511
(.branch 3530 53544
(.branch 3529 53545
.empty
.empty)
.empty)
(.branch 3532 60830
.empty
.empty))
(.branch 3535 60831
(.branch 3534 54864
.empty
.empty)
(.branch 3536 53606
.empty
.empty)))
(.branch 3542 60768
(.branch 3540 54830
(.branch 3539 53607
(.branch 3538 59544
.empty
.empty)
.empty)
(.branch 3541 60769
.empty
.empty))
(.branch 3544 59798
(.branch 3543 54831
.empty
.empty)
(.branch 3545 53449
.empty
.empty)))))
(.branch 3564 10399
(.branch 3555 53511
(.branch 3551 60927
(.branch 3549 54577
(.branch 3548 60926
(.branch 3547 59799
.empty
.empty)
.empty)
(.branch 3550 54576
.empty
.empty))
(.branch 3553 59833
(.branch 3552 53510
.empty
.empty)
(.branch 3554 59832
.empty
.empty)))
(.branch 3560 10183
(.branch 3558 60864
(.branch 3557 60865
(.branch 3556 54542
.empty
.empty)
.empty)
(.branch 3559 54543
.empty
.empty))
(.branch 3562 32998
(.branch 3561 32997
.empty
.empty)
(.branch 3563 10184
.empty
.empty))))
(.branch 3573 34674
(.branch 3569 34634
(.branch 3567 10352
(.branch 3566 33225
(.branch 3565 33226
.empty
.empty)
.empty)
(.branch 3568 607
.empty
.empty))
(.branch 3571 560
(.branch 3570 34633
.empty
.empty)
(.branch 3572 1125
.empty
.empty)))
(.branch 3578 33209
(.branch 3576 10403
(.branch 3575 1066
(.branch 3574 34673
.empty
.empty)
.empty)
(.branch 3577 33210
.empty
.empty))
(.branch 3580 10199
(.branch 3579 10348
.empty
.empty)
(.branch 3581 32938
.empty
.empty)))))))
(.branch 3654 34617
(.branch 3618 34717
(.branch 3600 604
(.branch 3591 556
(.branch 3587 1065
(.branch 3585 34670
(.branch 3584 1126
(.branch 3583 10168
.empty
.empty)
.empty)
(.branch 3586 34669
.empty
.empty))
(.branch 3589 34618
(.branch 3588 611
.empty
.empty)
(.branch 3590 34617
.empty
.empty)))
(.branch 3596 10351
(.branch 3594 32950
(.branch 3593 32949
(.branch 3592 10171
.empty
.empty)
.empty)
(.branch 3595 10196
.empty
.empty))
(.branch 3598 33222
(.branch 3597 33221
.empty
.empty)
(.branch 3599 10400
.empty
.empty))))
(.branch 3609 33237
(.branch 3605 34722
(.branch 3603 563
(.branch 3602 34645
(.branch 3601 34646
.empty
.empty)
.empty)
(.branch 3604 1113
.empty
.empty))
(.branch 3607 1078
(.branch 3606 34721
.empty
.empty)
(.branch 3608 10355
.empty
.empty)))
(.branch 3614 32985
(.branch 3612 10187
(.branch 3611 10396
(.branch 3610 33238
.empty
.empty)
.empty)
(.branch 3613 32986
.empty
.empty))
(.branch 3616 1114
(.branch 3615 10180
.empty
.empty)
(.branch 3617 34718
.empty
.empty)))))
(.branch 3636 1125
(.branch 3627 10184
(.branch 3623 559
(.branch 3621 34630
(.branch 3620 608
(.branch 3619 1077
.empty
.empty)
.empty)
(.branch 3622 34629
.empty
.empty))
(.branch 3625 32997
(.branch 3624 10183
.empty
.empty)
(.branch 3626 32998
.empty
.empty)))
(.branch 3632 607
(.branch 3630 33225
(.branch 3629 33226
(.branch 3628 10399
.empty
.empty)
.empty)
(.branch 3631 10352
.empty
.empty))
(.branch 3634 34633
(.branch 3633 34634
.empty
.empty)
(.branch 3635 560
.empty
.empty))))
(.branch 3645 32938
(.branch 3641 33210
(.branch 3639 1066
(.branch 3638 34673
(.branch 3637 34674
.empty
.empty)
.empty)
(.branch 3640 10403
.empty
.empty))
(.branch 3643 10348
(.branch 3642 33209
.empty
.empty)
(.branch 3644 10199
.empty
.empty)))
(.branch 3650 34669
(.branch 3648 1126
(.branch 3647 10168
(.branch 3646 32937
.empty
.empty)
.empty)
(.branch 3649 34670
.empty
.empty))
(.branch 3652 611
(.branch 3651 1065
.empty
.empty)
(.branch 3653 34618
.empty
.empty))))))
(.branch 3690 55214
(.branch 3672 10355
(.branch 3663 10400
(.branch 3659 10196
(.branch 3657 32949
(.branch 3656 10171
(.branch 3655 556
.empty
.empty)
.empty)
(.branch 3658 32950
.empty
.empty))
(.branch 3661 33221
(.branch 3660 10351
.empty
.empty)
(.branch 3662 33222
.empty
.empty)))
(.branch 3668 1113
(.branch 3666 34645
(.branch 3665 34646
(.branch 3664 604
.empty
.empty)
.empty)
(.branch 3667 563
.empty
.empty))
(.branch 3670 34721
(.branch 3669 34722
.empty
.empty)
(.branch 3671 1078
.empty
.empty))))
(.branch 3681 34718
(.branch 3677 32986
(.branch 3675 10396
(.branch 3674 33238
(.branch 3673 33237
.empty
.empty)
.empty)
(.branch 3676 10187
.empty
.empty))
(.branch 3679 10180
(.branch 3678 32985
.empty
.empty)
(.branch 3680 1114
.empty
.empty)))
(.branch 3686 34629
(.branch 3684 608
(.branch 3683 1077
(.branch 3682 34717
.empty
.empty)
.empty)
(.branch 3685 34630
.empty
.empty))
(.branch 3688 59175
(.branch 3687 559
.empty
.empty)
(.branch 3689 61167
.empty
.empty)))))
(.branch 3708 59113
(.branch 3699 61153
(.branch 3695 61152
(.branch 3693 53209
(.branch 3692 55201
(.branch 3691 53222
.empty
.empty)
.empty)
(.branch 3694 59160
.empty
.empty))
(.branch 3697 53208
(.branch 3696 55200
.empty
.empty)
(.branch 3698 59161
.empty
.empty)))
(.branch 3704 55263
(.branch 3702 55215
(.branch 3701 61166
(.branch 3700 59174
.empty
.empty)
.empty)
(.branch 3703 53223
.empty
.empty))
(.branch 3706 59126
(.branch 3705 53175
.empty
.empty)
(.branch 3707 61214
.empty
.empty))))
(.branch 3717 53174
(.branch 3713 61200
(.branch 3711 53160
(.branch 3710 55248
(.branch 3709 61201
.empty
.empty)
.empty)
(.branch 3712 59112
.empty
.empty))
(.branch 3715 53161
(.branch 3714 55249
.empty
.empty)
(.branch 3716 55262
.empty
.empty)))
(.branch 3721 59463
(.branch 3719 61215
(.branch 3718 59127
.empty
.empty)
(.branch 3720 61263
.empty
.empty))
(.branch 3723 54926
(.branch 3722 53126
.empty
.empty)
(.branch 3724 53113
.empty
.empty))))))))
(.branch 3868 48878
(.branch 3797 59462
(.branch 3761 53208
(.branch 3743 54960
(.branch 3734 53127
(.branch 3730 61249
(.branch 3728 53112
(.branch 3727 59448
(.branch 3726 61248
.empty
.empty)
.empty)
(.branch 3729 54912
.empty
.empty))
(.branch 3732 61262
(.branch 3731 59449
.empty
.empty)
(.branch 3733 59462
.empty
.empty)))
(.branch 3739 59414
(.branch 3737 54975
(.branch 3736 53079
(.branch 3735 54927
.empty
.empty)
.empty)
(.branch 3738 61310
.empty
.empty))
(.branch 3741 59401
(.branch 3740 61297
.empty
.empty)
(.branch 3742 53064
.empty
.empty))))
(.branch 3752 59175
(.branch 3748 53078
(.branch 3746 53065
(.branch 3745 59400
(.branch 3744 61296
.empty
.empty)
.empty)
(.branch 3747 54961
.empty
.empty))
(.branch 3750 61311
(.branch 3749 54974
.empty
.empty)
(.branch 3751 59415
.empty
.empty)))
(.branch 3757 53209
(.branch 3755 53222
(.branch 3754 55214
(.branch 3753 61167
.empty
.empty)
.empty)
(.branch 3756 55201
.empty
.empty))
(.branch 3759 61152
(.branch 3758 59160
.empty
.empty)
(.branch 3760 55200
.empty
.empty)))))
(.branch 3779 53161
(.branch 3770 59126
(.branch 3766 55215
(.branch 3764 59174
(.branch 3763 61153
(.branch 3762 59161
.empty
.empty)
.empty)
(.branch 3765 61166
.empty
.empty))
(.branch 3768 55263
(.branch 3767 53223
.empty
.empty)
(.branch 3769 53175
.empty
.empty)))
(.branch 3775 53160
(.branch 3773 61201
(.branch 3772 59113
(.branch 3771 61214
.empty
.empty)
.empty)
(.branch 3774 55248
.empty
.empty))
(.branch 3777 61200
(.branch 3776 59112
.empty
.empty)
(.branch 3778 55249
.empty
.empty))))
(.branch 3788 53113
(.branch 3784 61263
(.branch 3782 59127
(.branch 3781 53174
(.branch 3780 55262
.empty
.empty)
.empty)
(.branch 3783 61215
.empty
.empty))
(.branch 3786 53126
(.branch 3785 59463
.empty
.empty)
(.branch 3787 54926
.empty
.empty)))
(.branch 3793 54912
(.branch 3791 59448
(.branch 3790 61248
(.branch 3789 54913
.empty
.empty)
.empty)
(.branch 3792 53112
.empty
.empty))
(.branch 3795 59449
(.branch 3794 61249
.empty
.empty)
(.branch 3796 61262
.empty
.empty))))))
(.branch 3833 25670
(.branch 3815 59415
(.branch 3806 53064
(.branch 3802 61310
(.branch 3800 53079
(.branch 3799 54927
(.branch 3798 53127
.empty
.empty)
.empty)
(.branch 3801 54975
.empty
.empty))
(.branch 3804 61297
(.branch 3803 59414
.empty
.empty)
(.branch 3805 59401
.empty
.empty)))
(.branch 3811 54961
(.branch 3809 59400
(.branch 3808 61296
(.branch 3807 54960
.empty
.empty)
.empty)
(.branch 3810 53065
.empty
.empty))
(.branch 3813 54974
(.branch 3812 53078
.empty
.empty)
(.branch 3814 61311
.empty
.empty))))
(.branch 3824 47881
(.branch 3820 47882
(.branch 3818 26704
(.branch 3817 30800
(.branch 3816 31679
.empty
.empty)
.empty)
(.branch 3819 25663
.empty
.empty))
(.branch 3822 48901
(.branch 3821 47685
.empty
.empty)
(.branch 3823 48714
.empty
.empty)))
(.branch 3829 30784
(.branch 3827 48713
(.branch 3826 48902
(.branch 3825 47686
.empty
.empty)
.empty)
(.branch 3828 31695
.empty
.empty))
(.branch 3831 25679
(.branch 3830 26688
.empty
.empty)
(.branch 3832 26697
.empty
.empty)))))
(.branch 3851 25680
(.branch 3842 47853
(.branch 3838 47854
(.branch 3836 48929
(.branch 3835 30793
(.branch 3834 31686
.empty
.empty)
.empty)
(.branch 3837 48686
.empty
.empty))
(.branch 3840 48930
(.branch 3839 47713
.empty
.empty)
(.branch 3841 48685
.empty
.empty)))
(.branch 3847 30777
(.branch 3845 25686
(.branch 3844 26681
(.branch 3843 47714
.empty
.empty)
.empty)
(.branch 3846 31702
.empty
.empty))
(.branch 3849 30783
(.branch 3848 31696
.empty
.empty)
(.branch 3850 26687
.empty
.empty))))
(.branch 3860 31680
(.branch 3856 47878
(.branch 3854 48906
(.branch 3853 47690
(.branch 3852 47877
.empty
.empty)
.empty)
(.branch 3855 48709
.empty
.empty))
(.branch 3858 48905
(.branch 3857 47689
.empty
.empty)
(.branch 3859 48710
.empty
.empty)))
(.branch 3864 26694
(.branch 3862 26703
(.branch 3861 30799
.empty
.empty)
(.branch 3863 25664
.empty
.empty))
(.branch 3866 31689
(.branch 3865 25673
.empty
.empty)
(.branch 3867 30790
.empty
.empty)))))))
(.branch 3940 26710
(.branch 3904 48930
(.branch 3886 48901
(.branch 3877 25657
(.branch 3873 48738
(.branch 3871 47662
(.branch 3870 47905
(.branch 3869 48737
.empty
.empty)
.empty)
(.branch 3872 48877
.empty
.empty))
(.branch 3875 47661
(.branch 3874 47906
.empty
.empty)
(.branch 3876 26710
.empty
.empty)))
(.branch 3882 26704
(.branch 3880 31679
(.branch 3879 30806
(.branch 3878 31673
.empty
.empty)
.empty)
(.branch 3881 30800
.empty
.empty))
(.branch 3884 47882
(.branch 3883 25663
.empty
.empty)
(.branch 3885 47685
.empty
.empty))))
(.branch 3895 25679
(.branch 3891 48713
(.branch 3889 47686
(.branch 3888 47881
(.branch 3887 48714
.empty
.empty)
.empty)
(.branch 3890 48902
.empty
.empty))
(.branch 3893 30784
(.branch 3892 31695
.empty
.empty)
(.branch 3894 26688
.empty
.empty)))
(.branch 3900 48929
(.branch 3898 31686
(.branch 3897 25670
(.branch 3896 26697
.empty
.empty)
.empty)
(.branch 3899 30793
.empty
.empty))
(.branch 3902 47854
(.branch 3901 48686
.empty
.empty)
(.branch 3903 47713
.empty
.empty)))))
(.branch 3922 48905
(.branch 3913 30783
(.branch 3909 25686
(.branch 3907 47714
(.branch 3906 47853
(.branch 3905 48685
.empty
.empty)
.empty)
(.branch 3908 26681
.empty
.empty))
(.branch 3911 30777
(.branch 3910 31702
.empty
.empty)
(.branch 3912 31696
.empty
.empty)))
(.branch 3918 48906
(.branch 3916 47877
(.branch 3915 25680
(.branch 3914 26687
.empty
.empty)
.empty)
(.branch 3917 47690
.empty
.empty))
(.branch 3920 47878
(.branch 3919 48709
.empty
.empty)
(.branch 3921 47689
.empty
.empty))))
(.branch 3931 30790
(.branch 3927 25664
(.branch 3925 30799
(.branch 3924 31680
(.branch 3923 48710
.empty
.empty)
.empty)
(.branch 3926 26703
.empty
.empty))
(.branch 3929 25673
(.branch 3928 26694
.empty
.empty)
(.branch 3930 31689
.empty
.empty)))
(.branch 3936 48877
(.branch 3934 47905
(.branch 3933 48737
(.branch 3932 48878
.empty
.empty)
.empty)
(.branch 3935 47662
.empty
.empty))
(.branch 3938 47906
(.branch 3937 48738
.empty
.empty)
(.branch 3939 47661
.empty
.empty))))))
(.branch 3976 86990
(.branch 3958 89016
(.branch 3949 88729
(.branch 3945 95017
(.branch 3943 30806
(.branch 3942 31673
(.branch 3941 25657
.empty
.empty)
.empty)
(.branch 3944 88694
.empty
.empty))
(.branch 3947 88695
(.branch 3946 95016
.empty
.empty)
(.branch 3948 95078
.empty
.empty)))
(.branch 3954 94920
(.branch 3952 88982
(.branch 3951 95079
(.branch 3950 88728
.empty
.empty)
.empty)
(.branch 3953 94921
.empty
.empty))
(.branch 3956 94982
(.branch 3955 88983
.empty
.empty)
(.branch 3957 89017
.empty
.empty))))
(.branch 3967 93231
(.branch 3963 86943
(.branch 3961 93265
(.branch 3960 86942
(.branch 3959 94983
.empty
.empty)
.empty)
(.branch 3962 93264
.empty
.empty))
(.branch 3965 86881
(.branch 3964 93230
.empty
.empty)
(.branch 3966 86880
.empty
.empty)))
(.branch 3972 92942
(.branch 3970 92976
(.branch 3969 92977
(.branch 3968 87038
.empty
.empty)
.empty)
(.branch 3971 87039
.empty
.empty))
(.branch 3974 86976
(.branch 3973 86977
.empty
.empty)
(.branch 3975 92943
.empty
.empty)))))
(.branch 3994 94968
(.branch 3985 93217
(.branch 3981 87025
(.branch 3979 86991
(.branch 3978 92928
(.branch 3977 92929
.empty
.empty)
.empty)
(.branch 3980 92990
.empty
.empty))
(.branch 3983 92991
(.branch 3982 87024
.empty
.empty)
(.branch 3984 86894
.empty
.empty)))
(.branch 3990 86928
(.branch 3988 93278
(.branch 3987 86895
(.branch 3986 93216
.empty
.empty)
.empty)
(.branch 3989 86929
.empty
.empty))
(.branch 3992 89030
(.branch 3991 93279
.empty
.empty)
(.branch 3993 94969
.empty
.empty))))
(.branch 4003 88743
(.branch 3999 94935
(.branch 3997 88969
(.branch 3996 94934
(.branch 3995 89031
.empty
.empty)
.empty)
(.branch 3998 88968
.empty
.empty))
(.branch 4001 95065
(.branch 4000 88742
.empty
.empty)
(.branch 4002 95064
.empty
.empty)))
(.branch 4007 95031
(.branch 4005 88681
(.branch 4004 95030
.empty
.empty)
(.branch 4006 88680
.empty
.empty))
(.branch 4009 95017
(.branch 4008 88694
.empty
.empty)
(.branch 4010 95016
.empty
.empty)))))))))
(.branch 4298 54518
(.branch 4155 211
(.branch 4083 33057
(.branch 4047 92991
(.branch 4029 86881
(.branch 4020 94982
(.branch 4016 88982
(.branch 4014 88728
(.branch 4013 88729
(.branch 4012 95078
.empty
.empty)
.empty)
(.branch 4015 95079
.empty
.empty))
(.branch 4018 94920
(.branch 4017 94921
.empty
.empty)
(.branch 4019 88983
.empty
.empty)))
(.branch 4025 93265
(.branch 4023 94983
(.branch 4022 89016
(.branch 4021 89017
.empty
.empty)
.empty)
(.branch 4024 86942
.empty
.empty))
(.branch 4027 86943
(.branch 4026 93264
.empty
.empty)
(.branch 4028 93230
.empty
.empty))))
(.branch 4038 86976
(.branch 4034 92976
(.branch 4032 87038
(.branch 4031 93231
(.branch 4030 86880
.empty
.empty)
.empty)
(.branch 4033 92977
.empty
.empty))
(.branch 4036 92942
(.branch 4035 87039
.empty
.empty)
(.branch 4037 86977
.empty
.empty)))
(.branch 4043 86991
(.branch 4041 92929
(.branch 4040 86990
(.branch 4039 92943
.empty
.empty)
.empty)
(.branch 4042 92928
.empty
.empty))
(.branch 4045 87025
(.branch 4044 92990
.empty
.empty)
(.branch 4046 87024
.empty
.empty)))))
(.branch 4065 95065
(.branch 4056 89030
(.branch 4052 93278
(.branch 4050 93216
(.branch 4049 93217
(.branch 4048 86894
.empty
.empty)
.empty)
(.branch 4051 86895
.empty
.empty))
(.branch 4054 86928
(.branch 4053 86929
.empty
.empty)
(.branch 4055 93279
.empty
.empty)))
(.branch 4061 88969
(.branch 4059 89031
(.branch 4058 94968
(.branch 4057 94969
.empty
.empty)
.empty)
(.branch 4060 94934
.empty
.empty))
(.branch 4063 94935
(.branch 4062 88968
.empty
.empty)
(.branch 4064 88742
.empty
.empty))))
(.branch 4074 221
(.branch 4070 88680
(.branch 4068 95030
(.branch 4067 88743
(.branch 4066 95064
.empty
.empty)
.empty)
(.branch 4069 88681
.empty
.empty))
(.branch 4072 33028
(.branch 4071 95031
.empty
.empty)
(.branch 4073 33004
.empty
.empty)))
(.branch 4079 33058
(.branch 4077 23
(.branch 4076 310
(.branch 4075 332
.empty
.empty)
.empty)
(.branch 4078 33034
.empty
.empty))
(.branch 4081 1
(.branch 4080 288
.empty
.empty)
(.branch 4082 33033
.empty
.empty))))))
(.branch 4119 77
(.branch 4101 33019
(.branch 4092 24
(.branch 4088 33008
(.branch 4086 222
(.branch 4085 33059
(.branch 4084 33035
.empty
.empty)
.empty)
(.branch 4087 333
.empty
.empty))
(.branch 4090 352
(.branch 4089 33044
.empty
.empty)
(.branch 4091 211
.empty
.empty)))
(.branch 4097 287
(.branch 4095 33018
(.branch 4094 33054
(.branch 4093 309
.empty
.empty)
.empty)
(.branch 4096 2
.empty
.empty))
(.branch 4099 33017
(.branch 4098 33053
.empty
.empty)
(.branch 4100 33055
.empty
.empty))))
(.branch 4110 33046
(.branch 4106 487
(.branch 4104 33016
(.branch 4103 212
(.branch 4102 353
.empty
.empty)
.empty)
(.branch 4105 33052
.empty
.empty))
(.branch 4108 33
(.branch 4107 76
.empty
.empty)
(.branch 4109 300
.empty
.empty)))
(.branch 4115 33009
(.branch 4113 278
(.branch 4112 11
(.branch 4111 33010
.empty
.empty)
.empty)
(.branch 4114 33045
.empty
.empty))
(.branch 4117 33011
(.branch 4116 33047
.empty
.empty)
(.branch 4118 488
.empty
.empty)))))
(.branch 4137 33004
(.branch 4128 277
(.branch 4124 299
(.branch 4122 56
(.branch 4121 33032
(.branch 4120 33056
.empty
.empty)
.empty)
(.branch 4123 497
.empty
.empty))
(.branch 4126 33006
(.branch 4125 34
.empty
.empty)
(.branch 4127 33030
.empty
.empty)))
(.branch 4133 33031
(.branch 4131 33029
(.branch 4130 33005
(.branch 4129 12
.empty
.empty)
.empty)
(.branch 4132 33007
.empty
.empty))
(.branch 4135 498
(.branch 4134 57
.empty
.empty)
(.branch 4136 33028
.empty
.empty))))
(.branch 4146 33033
(.branch 4142 33034
(.branch 4140 310
(.branch 4139 332
(.branch 4138 221
.empty
.empty)
.empty)
(.branch 4141 23
.empty
.empty))
(.branch 4144 288
(.branch 4143 33058
.empty
.empty)
(.branch 4145 1
.empty
.empty)))
(.branch 4151 333
(.branch 4149 33059
(.branch 4148 33035
(.branch 4147 33057
.empty
.empty)
.empty)
(.branch 4150 222
.empty
.empty))
(.branch 4153 33044
(.branch 4152 33008
.empty
.empty)
(.branch 4154 352
.empty
.empty)))))))
(.branch 4227 60889
(.branch 4191 33030
(.branch 4173 300
(.branch 4164 33055
(.branch 4160 2
(.branch 4158 33054
(.branch 4157 309
(.branch 4156 24
.empty
.empty)
.empty)
(.branch 4159 33018
.empty
.empty))
(.branch 4162 33053
(.branch 4161 287
.empty
.empty)
(.branch 4163 33017
.empty
.empty)))
(.branch 4169 33052
(.branch 4167 212
(.branch 4166 353
(.branch 4165 33019
.empty
.empty)
.empty)
(.branch 4168 33016
.empty
.empty))
(.branch 4171 76
(.branch 4170 487
.empty
.empty)
(.branch 4172 33
.empty
.empty))))
(.branch 4182 488
(.branch 4178 33045
(.branch 4176 11
(.branch 4175 33010
(.branch 4174 33046
.empty
.empty)
.empty)
(.branch 4177 278
.empty
.empty))
(.branch 4180 33047
(.branch 4179 33009
.empty
.empty)
(.branch 4181 33011
.empty
.empty)))
(.branch 4187 497
(.branch 4185 33032
(.branch 4184 33056
(.branch 4183 77
.empty
.empty)
.empty)
(.branch 4186 56
.empty
.empty))
(.branch 4189 34
(.branch 4188 299
.empty
.empty)
(.branch 4190 33006
.empty
.empty)))))
(.branch 4209 53472
(.branch 4200 60759
(.branch 4196 33007
(.branch 4194 33005
(.branch 4193 12
(.branch 4192 277
.empty
.empty)
.empty)
(.branch 4195 33029
.empty
.empty))
(.branch 4198 57
(.branch 4197 33031
.empty
.empty)
(.branch 4199 498
.empty
.empty)))
(.branch 4205 53473
(.branch 4203 53486
(.branch 4202 54806
(.branch 4201 59823
.empty
.empty)
.empty)
(.branch 4204 54793
.empty
.empty))
(.branch 4207 59808
(.branch 4206 60744
.empty
.empty)
(.branch 4208 54792
.empty
.empty))))
(.branch 4218 53630
(.branch 4214 54807
(.branch 4212 60758
(.branch 4211 59809
(.branch 4210 60745
.empty
.empty)
.empty)
(.branch 4213 59822
.empty
.empty))
(.branch 4216 59583
(.branch 4215 53487
.empty
.empty)
(.branch 4217 60903
.empty
.empty)))
(.branch 4223 60888
(.branch 4221 54553
(.branch 4220 53617
(.branch 4219 54566
.empty
.empty)
.empty)
(.branch 4222 59568
.empty
.empty))
(.branch 4225 54552
(.branch 4224 53616
.empty
.empty)
(.branch 4226 59569
.empty
.empty))))))
(.branch 4263 54855
(.branch 4245 59534
(.branch 4236 54505
(.branch 4232 60855
(.branch 4230 53631
(.branch 4229 60902
(.branch 4228 59582
.empty
.empty)
.empty)
(.branch 4231 54567
.empty
.empty))
(.branch 4234 54518
(.branch 4233 59535
.empty
.empty)
(.branch 4235 53582
.empty
.empty)))
(.branch 4241 53568
(.branch 4239 59520
(.branch 4238 60840
(.branch 4237 53569
.empty
.empty)
.empty)
(.branch 4240 54504
.empty
.empty))
(.branch 4243 59521
(.branch 4242 60841
.empty
.empty)
(.branch 4244 60854
.empty
.empty))))
(.branch 4254 59856
(.branch 4250 53534
(.branch 4248 59871
(.branch 4247 53583
(.branch 4246 54519
.empty
.empty)
.empty)
(.branch 4249 60807
.empty
.empty))
(.branch 4252 53521
(.branch 4251 54854
.empty
.empty)
(.branch 4253 54841
.empty
.empty)))
(.branch 4259 60793
(.branch 4257 54840
(.branch 4256 53520
(.branch 4255 60792
.empty
.empty)
.empty)
(.branch 4258 59857
.empty
.empty))
(.branch 4261 60806
(.branch 4260 59870
.empty
.empty)
(.branch 4262 53535
.empty
.empty)))))
(.branch 4281 60903
(.branch 4272 54792
(.branch 4268 54793
(.branch 4266 54806
(.branch 4265 59823
(.branch 4264 60759
.empty
.empty)
.empty)
(.branch 4267 53486
.empty
.empty))
(.branch 4270 60744
(.branch 4269 53473
.empty
.empty)
(.branch 4271 59808
.empty
.empty)))
(.branch 4277 59822
(.branch 4275 59809
(.branch 4274 60745
(.branch 4273 53472
.empty
.empty)
.empty)
(.branch 4276 60758
.empty
.empty))
(.branch 4279 53487
(.branch 4278 54807
.empty
.empty)
(.branch 4280 59583
.empty
.empty))))
(.branch 4290 59569
(.branch 4286 59568
(.branch 4284 53617
(.branch 4283 54566
(.branch 4282 53630
.empty
.empty)
.empty)
(.branch 4285 54553
.empty
.empty))
(.branch 4288 53616
(.branch 4287 60888
.empty
.empty)
(.branch 4289 54552
.empty
.empty)))
(.branch 4294 53631
(.branch 4292 59582
(.branch 4291 60889
.empty
.empty)
(.branch 4293 60902
.empty
.empty))
(.branch 4296 60855
(.branch 4295 54567
.empty
.empty)
(.branch 4297 59535
.empty
.empty))))))))
(.branch 4441 30593
(.branch 4370 48974
(.branch 4334 48618
(.branch 4316 53521
(.branch 4307 59521
(.branch 4303 59520
(.branch 4301 53569
(.branch 4300 54505
(.branch 4299 53582
.empty
.empty)
.empty)
(.branch 4302 60840
.empty
.empty))
(.branch 4305 53568
(.branch 4304 54504
.empty
.empty)
(.branch 4306 60841
.empty
.empty)))
(.branch 4312 59871
(.branch 4310 54519
(.branch 4309 59534
(.branch 4308 60854
.empty
.empty)
.empty)
(.branch 4311 53583
.empty
.empty))
(.branch 4314 53534
(.branch 4313 60807
.empty
.empty)
(.branch 4315 54854
.empty
.empty))))
(.branch 4325 60806
(.branch 4321 54840
(.branch 4319 60792
(.branch 4318 59856
(.branch 4317 54841
.empty
.empty)
.empty)
(.branch 4320 53520
.empty
.empty))
(.branch 4323 60793
(.branch 4322 59857
.empty
.empty)
(.branch 4324 59870
.empty
.empty)))
(.branch 4330 25287
(.branch 4328 30600
(.branch 4327 54855
(.branch 4326 53535
.empty
.empty)
.empty)
(.branch 4329 30599
.empty
.empty))
(.branch 4332 47653
(.branch 4331 25288
.empty
.empty)
(.branch 4333 47594
.empty
.empty)))))
(.branch 4352 47913
(.branch 4343 25272
(.branch 4339 48678
(.branch 4337 47593
(.branch 4336 47654
(.branch 4335 48677
.empty
.empty)
.empty)
(.branch 4338 48617
.empty
.empty))
(.branch 4341 30615
(.branch 4340 30584
.empty
.empty)
(.branch 4342 25303
.empty
.empty)))
(.branch 4348 47914
(.branch 4346 27016
(.branch 4345 32072
(.branch 4344 32071
.empty
.empty)
.empty)
(.branch 4347 27015
.empty
.empty))
(.branch 4350 48997
(.branch 4349 47973
.empty
.empty)
(.branch 4351 48938
.empty
.empty))))
(.branch 4361 32078
(.branch 4357 32056
(.branch 4355 48937
(.branch 4354 48998
(.branch 4353 47974
.empty
.empty)
.empty)
(.branch 4356 32087
.empty
.empty))
(.branch 4359 27031
(.branch 4358 27000
.empty
.empty)
(.branch 4360 32065
.empty
.empty)))
(.branch 4366 48973
(.branch 4364 47938
(.branch 4363 27009
(.branch 4362 27022
.empty
.empty)
.empty)
(.branch 4365 47949
.empty
.empty))
(.branch 4368 47937
(.branch 4367 48962
.empty
.empty)
(.branch 4369 47950
.empty
.empty))))))
(.branch 4406 25303
(.branch 4388 30590
(.branch 4379 25294
(.branch 4375 27025
(.branch 4373 32062
(.branch 4372 32081
(.branch 4371 48961
.empty
.empty)
.empty)
(.branch 4374 27006
.empty
.empty))
(.branch 4377 30593
(.branch 4376 30606
.empty
.empty)
(.branch 4378 25281
.empty
.empty)))
(.branch 4384 47630
(.branch 4382 48642
(.branch 4381 47618
(.branch 4380 47629
.empty
.empty)
.empty)
(.branch 4383 48653
.empty
.empty))
(.branch 4386 48641
(.branch 4385 47617
.empty
.empty)
(.branch 4387 48654
.empty
.empty))))
(.branch 4397 47594
(.branch 4393 30599
(.branch 4391 25278
(.branch 4390 25297
(.branch 4389 30609
.empty
.empty)
.empty)
(.branch 4392 30600
.empty
.empty))
(.branch 4395 25288
(.branch 4394 25287
.empty
.empty)
(.branch 4396 47653
.empty
.empty)))
(.branch 4402 48617
(.branch 4400 47654
(.branch 4399 48677
(.branch 4398 48618
.empty
.empty)
.empty)
(.branch 4401 47593
.empty
.empty))
(.branch 4404 30584
(.branch 4403 48678
.empty
.empty)
(.branch 4405 30615
.empty
.empty)))))
(.branch 4424 32065
(.branch 4415 48938
(.branch 4411 27015
(.branch 4409 32072
(.branch 4408 32071
(.branch 4407 25272
.empty
.empty)
.empty)
(.branch 4410 27016
.empty
.empty))
(.branch 4413 47973
(.branch 4412 47914
.empty
.empty)
(.branch 4414 48997
.empty
.empty)))
(.branch 4420 32087
(.branch 4418 48998
(.branch 4417 47974
(.branch 4416 47913
.empty
.empty)
.empty)
(.branch 4419 48937
.empty
.empty))
(.branch 4422 27000
(.branch 4421 32056
.empty
.empty)
(.branch 4423 27031
.empty
.empty))))
(.branch 4433 47950
(.branch 4429 47949
(.branch 4427 27009
(.branch 4426 27022
(.branch 4425 32078
.empty
.empty)
.empty)
(.branch 4428 47938
.empty
.empty))
(.branch 4431 48962
(.branch 4430 48973
.empty
.empty)
(.branch 4432 47937
.empty
.empty)))
(.branch 4437 32062
(.branch 4435 48961
(.branch 4434 48974
.empty
.empty)
(.branch 4436 32081
.empty
.empty))
(.branch 4439 27025
(.branch 4438 27006
.empty
.empty)
(.branch 4440 30606
.empty
.empty)))))))
(.branch 4513 94992
(.branch 4477 95089
(.branch 4459 93206
(.branch 4450 48641
(.branch 4446 48642
(.branch 4444 47629
(.branch 4443 25294
(.branch 4442 25281
.empty
.empty)
.empty)
(.branch 4445 47618
.empty
.empty))
(.branch 4448 47630
(.branch 4447 48653
.empty
.empty)
(.branch 4449 47617
.empty
.empty)))
(.branch 4455 25278
(.branch 4453 30609
(.branch 4452 30590
(.branch 4451 48654
.empty
.empty)
.empty)
(.branch 4454 25297
.empty
.empty))
(.branch 4457 86871
(.branch 4456 93255
.empty
.empty)
(.branch 4458 86918
.empty
.empty))))
(.branch 4468 93254
(.branch 4464 86904
(.branch 4462 93240
(.branch 4461 93193
(.branch 4460 86905
.empty
.empty)
.empty)
(.branch 4463 86856
.empty
.empty))
(.branch 4466 93241
(.branch 4465 93192
.empty
.empty)
(.branch 4467 86857
.empty
.empty)))
(.branch 4473 88767
(.branch 4471 93207
(.branch 4470 86919
(.branch 4469 86870
.empty
.empty)
.empty)
(.branch 4472 95055
.empty
.empty))
(.branch 4475 95102
(.branch 4474 88718
.empty
.empty)
(.branch 4476 88705
.empty
.empty)))))
(.branch 4495 86952
(.branch 4486 88719
(.branch 4482 95041
(.branch 4480 88704
(.branch 4479 88752
(.branch 4478 95040
.empty
.empty)
.empty)
(.branch 4481 95088
.empty
.empty))
(.branch 4484 95054
(.branch 4483 88753
.empty
.empty)
(.branch 4485 88766
.empty
.empty)))
(.branch 4491 92918
(.branch 4489 86967
(.branch 4488 92967
(.branch 4487 95103
.empty
.empty)
.empty)
(.branch 4490 87014
.empty
.empty))
(.branch 4493 92905
(.branch 4492 87001
.empty
.empty)
(.branch 4494 92952
.empty
.empty))))
(.branch 4504 94959
(.branch 4500 92966
(.branch 4498 92953
(.branch 4497 92904
(.branch 4496 87000
.empty
.empty)
.empty)
(.branch 4499 86953
.empty
.empty))
(.branch 4502 87015
(.branch 4501 86966
.empty
.empty)
(.branch 4503 92919
.empty
.empty)))
(.branch 4509 94993
(.branch 4507 95006
(.branch 4506 89006
(.branch 4505 89055
.empty
.empty)
.empty)
(.branch 4508 88993
.empty
.empty))
(.branch 4511 89040
(.branch 4510 94944
.empty
.empty)
(.branch 4512 88992
.empty
.empty))))))
(.branch 4549 88766
(.branch 4531 86857
(.branch 4522 86918
(.branch 4518 89007
(.branch 4516 94958
(.branch 4515 89041
(.branch 4514 94945
.empty
.empty)
.empty)
(.branch 4517 89054
.empty
.empty))
(.branch 4520 93255
(.branch 4519 95007
.empty
.empty)
(.branch 4521 86871
.empty
.empty)))
(.branch 4527 86856
(.branch 4525 93193
(.branch 4524 86905
(.branch 4523 93206
.empty
.empty)
.empty)
(.branch 4526 93240
.empty
.empty))
(.branch 4529 93192
(.branch 4528 86904
.empty
.empty)
(.branch 4530 93241
.empty
.empty))))
(.branch 4540 88705
(.branch 4536 95055
(.branch 4534 86919
(.branch 4533 86870
(.branch 4532 93254
.empty
.empty)
.empty)
(.branch 4535 93207
.empty
.empty))
(.branch 4538 88718
(.branch 4537 88767
.empty
.empty)
(.branch 4539 95102
.empty
.empty)))
(.branch 4545 95088
(.branch 4543 88752
(.branch 4542 95040
(.branch 4541 95089
.empty
.empty)
.empty)
(.branch 4544 88704
.empty
.empty))
(.branch 4547 88753
(.branch 4546 95041
.empty
.empty)
(.branch 4548 95054
.empty
.empty)))))
(.branch 4567 92919
(.branch 4558 92952
(.branch 4554 87014
(.branch 4552 92967
(.branch 4551 95103
(.branch 4550 88719
.empty
.empty)
.empty)
(.branch 4553 86967
.empty
.empty))
(.branch 4556 87001
(.branch 4555 92918
.empty
.empty)
(.branch 4557 92905
.empty
.empty)))
(.branch 4563 86953
(.branch 4561 92904
(.branch 4560 87000
(.branch 4559 86952
.empty
.empty)
.empty)
(.branch 4562 92953
.empty
.empty))
(.branch 4565 86966
(.branch 4564 92966
.empty
.empty)
(.branch 4566 87015
.empty
.empty))))
(.branch 4576 88992
(.branch 4572 88993
(.branch 4570 89006
(.branch 4569 89055
(.branch 4568 94959
.empty
.empty)
.empty)
(.branch 4571 95006
.empty
.empty))
(.branch 4574 94944
(.branch 4573 94993
.empty
.empty)
(.branch 4575 89040
.empty
.empty)))
(.branch 4580 94958
(.branch 4578 94945
(.branch 4577 94992
.empty
.empty)
(.branch 4579 89041
.empty
.empty))
(.branch 4582 89007
(.branch 4581 89054
.empty
.empty)
(.branch 4583 95007
.empty
.empty))))))))))))

/-- Bounded lookup of the complete candidate original source labels for frame 1. -/
def generatedAxisGlobalOddFourthSelectedSourceTree01 : GeneratedAxisGlobalSparseLookupTree (Fin 98280) :=
  (.branch 2292 60301
(.branch 1146 32261
(.branch 573 34298
(.branch 286 33353
(.branch 143 33337
(.branch 71 3482
(.branch 35 10285
(.branch 17 3414
(.branch 8 1008
(.branch 4 3600
(.branch 2 3594
(.branch 1 528
(.branch 0 3593
.empty
.empty)
.empty)
(.branch 3 3603
.empty
.empty))
(.branch 6 550
(.branch 5 530
.empty
.empty)
(.branch 7 33365
.empty
.empty)))
(.branch 13 8982
(.branch 11 3408
(.branch 10 33366
(.branch 9 1026
.empty
.empty)
.empty)
(.branch 12 8976
.empty
.empty))
(.branch 15 8970
(.branch 14 3402
.empty
.empty)
(.branch 16 3404
.empty
.empty))))
(.branch 26 92
(.branch 22 1028
(.branch 20 33356
(.branch 19 1014
(.branch 18 8972
.empty
.empty)
.empty)
(.branch 21 33359
.empty
.empty))
(.branch 24 86
(.branch 23 3609
.empty
.empty)
(.branch 25 386
.empty
.empty)))
(.branch 31 3465
(.branch 29 34734
(.branch 28 3590
(.branch 27 3574
.empty
.empty)
.empty)
(.branch 30 3481
.empty
.empty))
(.branch 33 1157
(.branch 32 34733
.empty
.empty)
(.branch 34 10287
.empty
.empty)))))
(.branch 53 33382
(.branch 44 3449
(.branch 40 10336
(.branch 38 1173
(.branch 37 10338
(.branch 36 1181
.empty
.empty)
.empty)
(.branch 39 1133
.empty
.empty))
(.branch 42 34784
(.branch 41 3433
.empty
.empty)
(.branch 43 34787
.empty
.empty)))
(.branch 49 254
(.branch 47 3616
(.branch 46 3619
(.branch 45 3610
.empty
.empty)
.empty)
(.branch 48 274
.empty
.empty))
(.branch 51 1041
(.branch 50 33381
.empty
.empty)
(.branch 52 1059
.empty
.empty))))
(.branch 62 1047
(.branch 58 8986
(.branch 56 8998
(.branch 55 8992
(.branch 54 3424
.empty
.empty)
.empty)
(.branch 57 3418
.empty
.empty))
(.branch 60 3430
(.branch 59 3420
.empty
.empty)
(.branch 61 8988
.empty
.empty)))
(.branch 67 110
(.branch 65 1061
(.branch 64 33375
(.branch 63 33372
.empty
.empty)
.empty)
(.branch 66 368
.empty
.empty))
(.branch 69 3589
(.branch 68 3573
.empty
.empty)
(.branch 70 34738
.empty
.empty))))))
(.branch 107 34762
(.branch 89 34774
(.branch 80 1134
(.branch 76 10289
(.branch 74 1158
(.branch 73 34737
(.branch 72 3466
.empty
.empty)
.empty)
(.branch 75 10291
.empty
.empty))
(.branch 78 10334
(.branch 77 1182
.empty
.empty)
(.branch 79 1174
.empty
.empty)))
(.branch 85 3450
(.branch 83 34780
(.branch 82 3434
(.branch 81 10332
.empty
.empty)
.empty)
(.branch 84 34783
.empty
.empty))
(.branch 87 3564
(.branch 86 362
.empty
.empty)
(.branch 88 3580
.empty
.empty))))
(.branch 98 1144
(.branch 94 10327
(.branch 92 34773
(.branch 91 3475
(.branch 90 3491
.empty
.empty)
.empty)
(.branch 93 1160
.empty
.empty))
(.branch 96 1136
(.branch 95 10325
.empty
.empty)
(.branch 97 10298
.empty
.empty)))
(.branch 103 34747
(.branch 101 3443
(.branch 100 10296
(.branch 99 1184
.empty
.empty)
.empty)
(.branch 102 34744
.empty
.empty))
(.branch 105 3567
(.branch 104 3459
.empty
.empty)
(.branch 106 3583
.empty
.empty)))))
(.branch 125 1054
(.branch 116 1147
(.branch 112 10315
(.branch 110 34761
(.branch 109 3472
(.branch 108 3488
.empty
.empty)
.empty)
(.branch 111 1163
.empty
.empty))
(.branch 114 1139
(.branch 113 10313
.empty
.empty)
(.branch 115 10310
.empty
.empty)))
(.branch 121 34759
(.branch 119 3440
(.branch 118 10308
(.branch 117 1187
.empty
.empty)
.empty)
(.branch 120 34756
.empty
.empty))
(.branch 123 252
(.branch 122 3456
.empty
.empty)
(.branch 124 33322
.empty
.empty))))
(.branch 134 3369
(.branch 130 8937
(.branch 128 3375
(.branch 127 33321
(.branch 126 1036
.empty
.empty)
.empty)
(.branch 129 8943
.empty
.empty))
(.branch 132 8949
(.branch 131 3381
.empty
.empty)
(.branch 133 3379
.empty
.empty)))
(.branch 139 1034
(.branch 137 33331
(.branch 136 1048
(.branch 135 8947
.empty
.empty)
.empty)
(.branch 138 33328
.empty
.empty))
(.branch 141 1023
(.branch 140 33338
.empty
.empty)
(.branch 142 1005
.empty
.empty)))))))
(.branch 215 416
(.branch 179 3558
(.branch 161 33058
(.branch 152 1017
(.branch 148 8965
(.branch 146 8953
(.branch 145 8959
(.branch 144 3391
.empty
.empty)
.empty)
(.branch 147 3397
.empty
.empty))
(.branch 150 3385
(.branch 149 3395
.empty
.empty)
(.branch 151 8963
.empty
.empty)))
(.branch 157 33429
(.branch 155 1003
(.branch 154 33344
(.branch 153 33347
.empty
.empty)
.empty)
(.branch 156 33445
.empty
.empty))
(.branch 159 34570
(.branch 158 0
.empty
.empty)
(.branch 160 33034
.empty
.empty))))
(.branch 170 33413
(.branch 166 33018
(.branch 164 34554
(.branch 163 33010
(.branch 162 34546
.empty
.empty)
.empty)
(.branch 165 34594
.empty
.empty))
(.branch 168 290
(.branch 167 33397
.empty
.empty)
(.branch 169 36
.empty
.empty)))
(.branch 175 9062
(.branch 173 3552
(.branch 172 33446
(.branch 171 533
.empty
.empty)
.empty)
(.branch 174 9056
.empty
.empty))
(.branch 177 9050
(.branch 176 3546
.empty
.empty)
(.branch 178 3548
.empty
.empty)))))
(.branch 197 255
(.branch 188 9046
(.branch 184 538
(.branch 182 33436
(.branch 181 531
(.branch 180 9052
.empty
.empty)
.empty)
(.branch 183 33439
.empty
.empty))
(.branch 186 3536
(.branch 185 33430
.empty
.empty)
(.branch 187 9040
.empty
.empty)))
(.branch 193 9036
(.branch 191 3532
(.branch 190 9034
(.branch 189 3530
.empty
.empty)
.empty)
(.branch 192 3542
.empty
.empty))
(.branch 195 33420
(.branch 194 262
.empty
.empty)
(.branch 196 33423
.empty
.empty))))
(.branch 206 33398
(.branch 202 33009
(.branch 200 33057
(.branch 199 33033
(.branch 198 34569
.empty
.empty)
.empty)
(.branch 201 34545
.empty
.empty))
(.branch 204 34593
(.branch 203 34553
.empty
.empty)
(.branch 205 33017
.empty
.empty)))
(.branch 211 10249
(.branch 209 33414
(.branch 208 14
(.branch 207 312
.empty
.empty)
.empty)
(.branch 210 10251
.empty
.empty))
(.branch 213 10246
(.branch 212 141
.empty
.empty)
(.branch 214 156
.empty
.empty))))))
(.branch 251 9002
(.branch 233 10233
(.branch 224 10235
(.branch 220 3520
(.branch 218 34564
(.branch 217 3504
(.branch 216 10244
.empty
.empty)
.empty)
(.branch 219 34567
.empty
.empty))
(.branch 222 10227
(.branch 221 350
.empty
.empty)
(.branch 223 75
.empty
.empty)))
(.branch 229 33031
(.branch 227 9008
(.branch 226 210
(.branch 225 10275
.empty
.empty)
.empty)
(.branch 228 33028
.empty
.empty))
(.branch 231 10225
(.branch 230 9024
.empty
.empty)
(.branch 232 486
.empty
.empty))))
(.branch 242 432
(.branch 238 33007
(.branch 236 9014
(.branch 235 351
(.branch 234 10273
.empty
.empty)
.empty)
(.branch 237 33004
.empty
.empty))
(.branch 240 10270
(.branch 239 9030
.empty
.empty)
(.branch 241 140
.empty
.empty)))
(.branch 247 3514
(.branch 245 34588
(.branch 244 3498
(.branch 243 10268
.empty
.empty)
.empty)
(.branch 246 34591
.empty
.empty))
(.branch 249 10222
(.branch 248 10262
.empty
.empty)
(.branch 250 74
.empty
.empty)))))
(.branch 269 9020
(.branch 260 3516
(.branch 256 10260
(.branch 254 9018
(.branch 253 33055
(.branch 252 33052
.empty
.empty)
.empty)
(.branch 255 417
.empty
.empty))
(.branch 258 34580
(.branch 257 3500
.empty
.empty)
(.branch 259 34583
.empty
.empty)))
(.branch 265 3526
(.branch 263 34540
(.branch 262 3510
(.branch 261 10220
.empty
.empty)
.empty)
(.branch 264 34543
.empty
.empty))
(.branch 267 33044
(.branch 266 9004
.empty
.empty)
(.branch 268 33047
.empty
.empty))))
(.branch 278 3605
(.branch 274 33404
(.branch 272 257
(.branch 271 33391
(.branch 270 33388
.empty
.empty)
.empty)
(.branch 273 276
.empty
.empty))
(.branch 276 3606
(.branch 275 33407
.empty
.empty)
(.branch 277 269
.empty
.empty)))
(.branch 282 250
(.branch 280 3599
(.branch 279 3596
.empty
.empty)
(.branch 281 267
.empty
.empty))
(.branch 284 1030
(.branch 283 33354
.empty
.empty)
(.branch 285 1012
.empty
.empty))))))))
(.branch 430 33343
(.branch 358 3445
(.branch 322 3612
(.branch 304 3577
(.branch 295 1024
(.branch 291 8981
(.branch 289 8969
(.branch 288 8975
(.branch 287 3407
.empty
.empty)
.empty)
(.branch 290 3413
.empty
.empty))
(.branch 293 3401
(.branch 292 3411
.empty
.empty)
(.branch 294 8979
.empty
.empty)))
(.branch 300 461
(.branch 298 1010
(.branch 297 33360
(.branch 296 33363
.empty
.empty)
.empty)
(.branch 299 3622
.empty
.empty))
(.branch 302 385
(.branch 301 91
.empty
.empty)
(.branch 303 3561
.empty
.empty))))
(.branch 313 10286
(.branch 309 1161
(.branch 307 3478
(.branch 306 3494
(.branch 305 34786
.empty
.empty)
.empty)
(.branch 308 34785
.empty
.empty))
(.branch 311 10337
(.branch 310 10339
.empty
.empty)
(.branch 312 1137
.empty
.empty)))
(.branch 318 34732
(.branch 316 10284
(.branch 315 1185
(.branch 314 1145
.empty
.empty)
.empty)
(.branch 317 3446
.empty
.empty))
(.branch 320 3462
(.branch 319 34735
.empty
.empty)
(.branch 321 3621
.empty
.empty)))))
(.branch 340 33376
(.branch 331 8991
(.branch 327 1063
(.branch 325 543
(.branch 324 526
(.branch 323 3615
.empty
.empty)
.empty)
(.branch 326 33370
.empty
.empty))
(.branch 329 33369
(.branch 328 1045
.empty
.empty)
(.branch 330 3423
.empty
.empty)))
(.branch 336 3417
(.branch 334 8997
(.branch 333 3429
(.branch 332 8985
.empty
.empty)
.empty)
(.branch 335 3427
.empty
.empty))
(.branch 338 1057
(.branch 337 8995
.empty
.empty)
(.branch 339 33379
.empty
.empty))))
(.branch 349 34781
(.branch 345 3578
(.branch 343 367
(.branch 342 109
(.branch 341 1043
.empty
.empty)
.empty)
(.branch 344 3562
.empty
.empty))
(.branch 347 3493
(.branch 346 34782
.empty
.empty)
(.branch 348 3477
.empty
.empty)))
(.branch 354 10290
(.branch 352 10333
(.branch 351 10335
(.branch 350 1162
.empty
.empty)
.empty)
(.branch 353 1138
.empty
.empty))
(.branch 356 1186
(.branch 355 1146
.empty
.empty)
(.branch 357 10288
.empty
.empty))))))
(.branch 394 10312
(.branch 376 10324
(.branch 367 3468
(.branch 363 3571
(.branch 361 3461
(.branch 360 34739
(.branch 359 34736
.empty
.empty)
.empty)
(.branch 362 185
.empty
.empty))
(.branch 365 34746
(.branch 364 3587
.empty
.empty)
(.branch 366 3484
.empty
.empty)))
(.branch 372 1180
(.branch 370 10299
(.branch 369 1156
(.branch 368 34745
.empty
.empty)
.empty)
(.branch 371 10297
.empty
.empty))
(.branch 374 1172
(.branch 373 10326
.empty
.empty)
(.branch 375 1132
.empty
.empty))))
(.branch 385 3471
(.branch 381 3568
(.branch 379 34775
(.branch 378 34772
(.branch 377 3436
.empty
.empty)
.empty)
(.branch 380 3452
.empty
.empty))
(.branch 383 34758
(.branch 382 3584
.empty
.empty)
(.branch 384 3487
.empty
.empty)))
(.branch 390 1183
(.branch 388 10311
(.branch 387 1159
(.branch 386 34757
.empty
.empty)
.empty)
(.branch 389 10309
.empty
.empty))
(.branch 392 1175
(.branch 391 10314
.empty
.empty)
(.branch 393 1135
.empty
.empty)))))
(.branch 412 1038
(.branch 403 33334
(.branch 399 545
(.branch 397 34763
(.branch 396 34760
(.branch 395 3439
.empty
.empty)
.empty)
(.branch 398 3455
.empty
.empty))
(.branch 401 1032
(.branch 400 33333
.empty
.empty)
(.branch 402 1050
.empty
.empty)))
(.branch 408 8938
(.branch 406 8950
(.branch 405 8944
(.branch 404 3376
.empty
.empty)
.empty)
(.branch 407 3370
.empty
.empty))
(.branch 410 3382
(.branch 409 3372
.empty
.empty)
(.branch 411 8940
.empty
.empty))))
(.branch 421 8960
(.branch 417 1001
(.branch 415 1052
(.branch 414 33327
(.branch 413 33324
.empty
.empty)
.empty)
(.branch 416 33349
.empty
.empty))
(.branch 419 33350
(.branch 418 1019
.empty
.empty)
(.branch 420 3392
.empty
.empty)))
(.branch 426 3398
(.branch 424 8954
(.branch 423 3386
(.branch 422 8966
.empty
.empty)
.empty)
(.branch 425 3388
.empty
.empty))
(.branch 428 1007
(.branch 427 8956
.empty
.empty)
(.branch 429 33340
.empty
.empty)))))))
(.branch 502 321
(.branch 466 9045
(.branch 448 33433
(.branch 439 33054
(.branch 435 34566
(.branch 433 33418
(.branch 432 33434
(.branch 431 1021
.empty
.empty)
.empty)
(.branch 434 507
.empty
.empty))
(.branch 437 33006
(.branch 436 33030
.empty
.empty)
(.branch 438 34590
.empty
.empty)))
(.branch 444 35
(.branch 442 33046
(.branch 441 34542
(.branch 440 34582
.empty
.empty)
.empty)
(.branch 443 33386
.empty
.empty))
(.branch 446 33402
(.branch 445 289
.empty
.empty)
(.branch 447 264
.empty
.empty))))
(.branch 457 271
(.branch 453 9061
(.branch 451 9049
(.branch 450 9055
(.branch 449 3551
.empty
.empty)
.empty)
(.branch 452 3557
.empty
.empty))
(.branch 455 3545
(.branch 454 3555
.empty
.empty)
(.branch 456 9059
.empty
.empty)))
(.branch 462 3535
(.branch 460 259
(.branch 459 33440
(.branch 458 33443
.empty
.empty)
.empty)
(.branch 461 33417
.empty
.empty))
(.branch 464 9033
(.branch 463 9039
.empty
.empty)
(.branch 465 3541
.empty
.empty)))))
(.branch 484 311
(.branch 475 33029
(.branch 471 33427
(.branch 469 9043
(.branch 468 3529
(.branch 467 3539
.empty
.empty)
.empty)
(.branch 470 535
.empty
.empty))
(.branch 473 547
(.branch 472 33424
.empty
.empty)
(.branch 474 34565
.empty
.empty)))
(.branch 480 34541
(.branch 478 33053
(.branch 477 34589
(.branch 476 33005
.empty
.empty)
.empty)
(.branch 479 34581
.empty
.empty))
(.branch 482 33385
(.branch 481 33045
.empty
.empty)
(.branch 483 13
.empty
.empty))))
(.branch 493 3503
(.branch 489 10250
(.branch 487 10245
(.branch 486 10247
(.branch 485 33401
.empty
.empty)
.empty)
(.branch 488 400
.empty
.empty))
(.branch 491 125
(.branch 490 399
.empty
.empty)
(.branch 492 10248
.empty
.empty)))
(.branch 498 10271
(.branch 496 3519
(.branch 495 34571
(.branch 494 34568
.empty
.empty)
.empty)
(.branch 497 55
.empty
.empty))
(.branch 500 10263
(.branch 499 330
.empty
.empty)
(.branch 501 10223
.empty
.empty))))))
(.branch 538 3497
(.branch 520 3509
(.branch 511 54
(.branch 507 10269
(.branch 505 33035
(.branch 504 33032
(.branch 503 9007
.empty
.empty)
.empty)
(.branch 506 9023
.empty
.empty))
(.branch 509 10261
(.branch 508 45
.empty
.empty)
(.branch 510 10221
.empty
.empty)))
(.branch 516 10226
(.branch 514 33059
(.branch 513 33056
(.branch 512 9001
.empty
.empty)
.empty)
(.branch 515 9017
.empty
.empty))
(.branch 518 123
(.branch 517 401
.empty
.empty)
(.branch 519 10224
.empty
.empty))))
(.branch 529 33011
(.branch 525 10274
(.branch 523 3525
(.branch 522 34547
(.branch 521 34544
.empty
.empty)
.empty)
(.branch 524 10234
.empty
.empty))
(.branch 527 9013
(.branch 526 331
.empty
.empty)
(.branch 528 33008
.empty
.empty)))
(.branch 534 34552
(.branch 532 10232
(.branch 531 124
(.branch 530 9029
.empty
.empty)
.empty)
(.branch 533 3507
.empty
.empty))
(.branch 536 3523
(.branch 535 34555
.empty
.empty)
(.branch 537 10272
.empty
.empty)))))
(.branch 556 1606
(.branch 547 33392
(.branch 543 33016
(.branch 541 3513
(.branch 540 34595
(.branch 539 34592
.empty
.empty)
.empty)
(.branch 542 9011
.empty
.empty))
(.branch 545 9027
(.branch 544 33019
.empty
.empty)
(.branch 546 33395
.empty
.empty)))
(.branch 552 1206
(.branch 550 33411
(.branch 549 231
(.branch 548 540
.empty
.empty)
.empty)
(.branch 551 33408
.empty
.empty))
(.branch 554 2935
(.branch 553 2932
.empty
.empty)
(.branch 555 1205
.empty
.empty))))
(.branch 565 2939
(.branch 561 3099
(.branch 559 1605
(.branch 558 3080
(.branch 557 3083
.empty
.empty)
.empty)
(.branch 560 1625
.empty
.empty))
(.branch 563 1626
(.branch 562 3096
.empty
.empty)
(.branch 564 1209
.empty
.empty)))
(.branch 569 34474
(.branch 567 1210
(.branch 566 2936
.empty
.empty)
(.branch 568 33650
.empty
.empty))
(.branch 571 33646
(.branch 570 34486
.empty
.empty)
(.branch 572 33613
.empty
.empty)))))))))
(.branch 860 86715
(.branch 717 32069
(.branch 645 31962
(.branch 609 34309
(.branch 591 1637
(.branch 582 34489
(.branch 578 34329
(.branch 576 33629
(.branch 575 33617
(.branch 574 34310
.empty
.empty)
.empty)
(.branch 577 34341
.empty
.empty))
(.branch 580 33661
(.branch 579 33633
.empty
.empty)
(.branch 581 34501
.empty
.empty)))
(.branch 587 1221
(.branch 585 2948
(.branch 584 1222
(.branch 583 33665
.empty
.empty)
.empty)
(.branch 586 2951
.empty
.empty))
(.branch 589 3108
(.branch 588 1638
.empty
.empty)
(.branch 590 3111
.empty
.empty))))
(.branch 600 33666
(.branch 596 1193
(.branch 594 3095
(.branch 593 3092
(.branch 592 1593
.empty
.empty)
.empty)
(.branch 595 1594
.empty
.empty))
(.branch 598 2920
(.branch 597 2923
.empty
.empty)
(.branch 599 1194
.empty
.empty)))
(.branch 605 34330
(.branch 603 33662
(.branch 602 34502
(.branch 601 34490
.empty
.empty)
.empty)
(.branch 604 33634
.empty
.empty))
(.branch 607 33630
(.branch 606 34342
.empty
.empty)
(.branch 608 33618
.empty
.empty)))))
(.branch 627 26624
(.branch 618 25891
(.branch 614 34473
(.branch 612 33645
(.branch 611 33614
(.branch 610 34297
.empty
.empty)
.empty)
(.branch 613 34485
.empty
.empty))
(.branch 616 25635
(.branch 615 33649
.empty
.empty)
(.branch 617 26600
.empty
.empty)))
(.branch 623 25836
(.branch 621 25580
(.branch 620 26663
(.branch 619 26748
.empty
.empty)
.empty)
(.branch 622 26771
.empty
.empty))
(.branch 625 26746
(.branch 624 25893
.empty
.empty)
(.branch 626 25611
.empty
.empty))))
(.branch 636 30851
(.branch 632 31751
(.branch 630 26639
(.branch 629 25834
(.branch 628 26773
.empty
.empty)
.empty)
(.branch 631 25604
.empty
.empty))
(.branch 634 31923
(.branch 633 30860
.empty
.empty)
(.branch 635 30924
.empty
.empty)))
(.branch 641 30922
(.branch 639 31964
(.branch 638 30915
(.branch 637 31752
.empty
.empty)
.empty)
(.branch 640 31925
.empty
.empty))
(.branch 643 30884
(.branch 642 31727
.empty
.empty)
(.branch 644 30917
.empty
.empty))))))
(.branch 681 48959
(.branch 663 25602
(.branch 654 26779
(.branch 650 25867
(.branch 648 25637
(.branch 647 31776
(.branch 646 30827
.empty
.empty)
.empty)
(.branch 649 26606
.empty
.empty))
(.branch 652 26657
(.branch 651 26740
.empty
.empty)
(.branch 653 25578
.empty
.empty)))
(.branch 659 26630
(.branch 657 26738
(.branch 656 25869
(.branch 655 25860
.empty
.empty)
.empty)
(.branch 658 25613
.empty
.empty))
(.branch 661 25858
(.branch 660 26781
.empty
.empty)
(.branch 662 26633
.empty
.empty))))
(.branch 672 31933
(.branch 668 30853
(.branch 666 31931
(.branch 665 30858
(.branch 664 31745
.empty
.empty)
.empty)
(.branch 667 30948
.empty
.empty))
(.branch 670 30891
(.branch 669 31758
.empty
.empty)
(.branch 671 31956
.empty
.empty)))
(.branch 677 31954
(.branch 675 30882
(.branch 674 31721
(.branch 673 30946
.empty
.empty)
.empty)
(.branch 676 30893
.empty
.empty))
(.branch 679 31782
(.branch 678 30829
.empty
.empty)
(.branch 680 25295
.empty
.empty)))))
(.branch 699 47931
(.branch 690 32074
(.branch 686 25302
(.branch 684 47655
(.branch 683 32076
(.branch 682 47619
.empty
.empty)
.empty)
(.branch 685 32085
.empty
.empty))
(.branch 688 48951
(.branch 687 48987
.empty
.empty)
(.branch 689 25289
.empty
.empty)))
(.branch 695 25296
(.branch 693 47631
(.branch 692 32083
(.branch 691 47595
.empty
.empty)
.empty)
(.branch 694 48979
.empty
.empty))
(.branch 697 27021
(.branch 696 48647
.empty
.empty)
(.branch 698 30606
.empty
.empty))))
(.branch 708 47959
(.branch 704 27019
(.branch 702 48675
(.branch 701 47967
(.branch 700 30615
.empty
.empty)
.empty)
(.branch 703 27028
.empty
.empty))
(.branch 706 47923
(.branch 705 48623
.empty
.empty)
(.branch 707 30600
.empty
.empty)))
(.branch 713 48956
(.branch 711 48651
(.branch 710 27026
(.branch 709 30609
.empty
.empty)
.empty)
(.branch 712 25279
.empty
.empty))
(.branch 715 32060
(.branch 714 47616
.empty
.empty)
(.branch 716 47652
.empty
.empty)))))))
(.branch 789 88134
(.branch 753 88137
(.branch 735 27012
(.branch 726 48976
(.branch 722 32058
(.branch 720 48948
(.branch 719 48984
(.branch 718 25286
.empty
.empty)
.empty)
(.branch 721 25273
.empty
.empty))
(.branch 724 32067
(.branch 723 47592
.empty
.empty)
(.branch 725 47628
.empty
.empty)))
(.branch 731 47928
(.branch 729 27005
(.branch 728 48644
(.branch 727 25280
.empty
.empty)
.empty)
(.branch 730 30590
.empty
.empty))
(.branch 733 47964
(.branch 732 30599
.empty
.empty)
(.branch 734 48672
.empty
.empty))))
(.branch 744 88086
(.branch 740 47956
(.branch 738 47920
(.branch 737 48620
(.branch 736 27003
.empty
.empty)
.empty)
(.branch 739 30584
.empty
.empty))
(.branch 742 27010
(.branch 741 30593
.empty
.empty)
(.branch 743 48648
.empty
.empty)))
(.branch 749 88135
(.branch 747 86286
(.branch 746 94134
(.branch 745 92334
.empty
.empty)
.empty)
(.branch 748 92287
.empty
.empty))
(.branch 751 94375
(.branch 750 86047
.empty
.empty)
(.branch 752 92289
.empty
.empty)))))
(.branch 771 94425
(.branch 762 94086
(.branch 758 94136
(.branch 756 88088
(.branch 755 94377
(.branch 754 86049
.empty
.empty)
.empty)
(.branch 757 92336
.empty
.empty))
(.branch 760 88038
(.branch 759 86288
.empty
.empty)
(.branch 761 92382
.empty
.empty)))
(.branch 767 94423
(.branch 765 88183
(.branch 764 92239
(.branch 763 86334
.empty
.empty)
.empty)
(.branch 766 85999
.empty
.empty))
(.branch 769 88185
(.branch 768 92241
.empty
.empty)
(.branch 770 86001
.empty
.empty))))
(.branch 780 88089
(.branch 776 92288
(.branch 774 94088
(.branch 773 92384
(.branch 772 88040
.empty
.empty)
.empty)
(.branch 775 86336
.empty
.empty))
(.branch 778 86048
(.branch 777 88136
.empty
.empty)
(.branch 779 94376
.empty
.empty)))
(.branch 785 92335
(.branch 783 86289
(.branch 782 94137
(.branch 781 92337
.empty
.empty)
.empty)
(.branch 784 88087
.empty
.empty))
(.branch 787 86287
(.branch 786 94135
.empty
.empty)
(.branch 788 92286
.empty
.empty))))))
(.branch 825 86426
(.branch 807 94422
(.branch 798 94089
(.branch 794 86000
(.branch 792 92240
(.branch 791 94374
(.branch 790 86046
.empty
.empty)
.empty)
(.branch 793 88184
.empty
.empty))
(.branch 796 88041
(.branch 795 94424
.empty
.empty)
(.branch 797 92385
.empty
.empty)))
(.branch 803 86335
(.branch 801 92383
(.branch 800 88039
(.branch 799 86337
.empty
.empty)
.empty)
(.branch 802 94087
.empty
.empty))
(.branch 805 88182
(.branch 804 92238
.empty
.empty)
(.branch 806 85998
.empty
.empty))))
(.branch 816 93987
(.branch 812 93996
(.branch 810 86378
(.branch 809 87794
(.branch 808 87698
.empty
.empty)
.empty)
(.branch 811 86666
.empty
.empty))
(.branch 814 92772
(.branch 813 93708
.empty
.empty)
(.branch 815 92676
.empty
.empty)))
(.branch 821 87805
(.branch 819 92667
(.branch 818 92763
(.branch 817 93699
.empty
.empty)
.empty)
(.branch 820 87709
.empty
.empty))
(.branch 823 86677
(.branch 822 86389
.empty
.empty)
(.branch 824 86714
.empty
.empty)))))
(.branch 843 92677
(.branch 834 93747
(.branch 830 93756
(.branch 828 92628
(.branch 827 87650
(.branch 826 87746
.empty
.empty)
.empty)
(.branch 829 92724
.empty
.empty))
(.branch 832 92619
(.branch 831 94044
.empty
.empty)
(.branch 833 92715
.empty
.empty)))
(.branch 839 87661
(.branch 837 86437
(.branch 836 86725
(.branch 835 94035
.empty
.empty)
.empty)
(.branch 838 87757
.empty
.empty))
(.branch 841 93709
(.branch 840 93997
.empty
.empty)
(.branch 842 92773
.empty
.empty))))
(.branch 852 93986
(.branch 848 87708
(.branch 846 86379
(.branch 845 87795
(.branch 844 87699
.empty
.empty)
.empty)
(.branch 847 86667
.empty
.empty))
(.branch 850 86388
(.branch 849 87804
.empty
.empty)
(.branch 851 86676
.empty
.empty)))
(.branch 856 92629
(.branch 854 92762
(.branch 853 93698
.empty
.empty)
(.branch 855 92666
.empty
.empty))
(.branch 858 93757
(.branch 857 92725
.empty
.empty)
(.branch 859 94045
.empty
.empty))))))))
(.branch 1003 10208
(.branch 932 88082
(.branch 896 88083
(.branch 878 86052
(.branch 869 92714
(.branch 865 86436
(.branch 863 87651
(.branch 862 87747
(.branch 861 86427
.empty
.empty)
.empty)
(.branch 864 86724
.empty
.empty))
(.branch 867 87660
(.branch 866 87756
.empty
.empty)
(.branch 868 92618
.empty
.empty)))
(.branch 874 85994
(.branch 872 92234
(.branch 871 94034
(.branch 870 93746
.empty
.empty)
.empty)
(.branch 873 88178
.empty
.empty))
(.branch 876 92292
(.branch 875 94418
.empty
.empty)
(.branch 877 88140
.empty
.empty))))
(.branch 887 94429
(.branch 883 94371
(.branch 881 88131
(.branch 880 92283
(.branch 879 94380
.empty
.empty)
.empty)
(.branch 882 86043
.empty
.empty))
(.branch 885 88189
(.branch 884 92245
.empty
.empty)
(.branch 886 86005
.empty
.empty)))
(.branch 892 88092
(.branch 890 94082
(.branch 889 92378
(.branch 888 88034
.empty
.empty)
.empty)
(.branch 891 86330
.empty
.empty))
(.branch 894 94140
(.branch 893 92340
.empty
.empty)
(.branch 895 86292
.empty
.empty)))))
(.branch 914 86004
(.branch 905 88141
(.branch 901 92389
(.branch 899 86283
(.branch 898 94131
(.branch 897 92331
.empty
.empty)
.empty)
(.branch 900 88045
.empty
.empty))
(.branch 903 86341
(.branch 902 94093
.empty
.empty)
(.branch 904 92293
.empty
.empty)))
(.branch 910 85995
(.branch 908 92235
(.branch 907 94381
(.branch 906 86053
.empty
.empty)
.empty)
(.branch 909 88179
.empty
.empty))
(.branch 912 92244
(.branch 911 94419
.empty
.empty)
(.branch 913 88188
.empty
.empty))))
(.branch 923 86293
(.branch 919 94370
(.branch 917 88130
(.branch 916 92282
(.branch 915 94428
.empty
.empty)
.empty)
(.branch 918 86042
.empty
.empty))
(.branch 921 92341
(.branch 920 88093
.empty
.empty)
(.branch 922 94141
.empty
.empty)))
(.branch 928 88044
(.branch 926 94083
(.branch 925 92379
(.branch 924 88035
.empty
.empty)
.empty)
(.branch 927 86331
.empty
.empty))
(.branch 930 94092
(.branch 929 92388
.empty
.empty)
(.branch 931 86340
.empty
.empty))))))
(.branch 968 93992
(.branch 950 93752
(.branch 941 93703
(.branch 937 92718
(.branch 935 86282
(.branch 934 94130
(.branch 933 92330
.empty
.empty)
.empty)
(.branch 936 92622
.empty
.empty))
(.branch 939 94038
(.branch 938 93750
.empty
.empty)
(.branch 940 93991
.empty
.empty)))
(.branch 946 92769
(.branch 944 93993
(.branch 943 92671
(.branch 942 92767
.empty
.empty)
.empty)
(.branch 945 93705
.empty
.empty))
(.branch 948 92624
(.branch 947 92673
.empty
.empty)
(.branch 949 92720
.empty
.empty))))
(.branch 959 86671
(.branch 955 87654
(.branch 953 86430
(.branch 952 86718
(.branch 951 94040
.empty
.empty)
.empty)
(.branch 954 87750
.empty
.empty))
(.branch 957 87799
(.branch 956 87703
.empty
.empty)
(.branch 958 86383
.empty
.empty)))
(.branch 964 86720
(.branch 962 86385
(.branch 961 87801
(.branch 960 87705
.empty
.empty)
.empty)
(.branch 963 86673
.empty
.empty))
(.branch 966 87752
(.branch 965 86432
.empty
.empty)
(.branch 967 87656
.empty
.empty)))))
(.branch 986 86384
(.branch 977 92719
(.branch 973 92721
(.branch 971 92672
(.branch 970 92768
(.branch 969 93704
.empty
.empty)
.empty)
(.branch 972 92625
.empty
.empty))
(.branch 975 94041
(.branch 974 93753
.empty
.empty)
(.branch 976 92623
.empty
.empty)))
(.branch 982 92766
(.branch 980 93990
(.branch 979 94039
(.branch 978 93751
.empty
.empty)
.empty)
(.branch 981 93702
.empty
.empty))
(.branch 984 87704
(.branch 983 92670
.empty
.empty)
(.branch 985 87800
.empty
.empty))))
(.branch 995 87655
(.branch 991 87657
(.branch 989 86433
(.branch 988 86721
(.branch 987 86672
.empty
.empty)
.empty)
(.branch 990 87753
.empty
.empty))
(.branch 993 86431
(.branch 992 86719
.empty
.empty)
(.branch 994 87751
.empty
.empty)))
(.branch 999 86670
(.branch 997 87798
(.branch 996 87702
.empty
.empty)
(.branch 998 86382
.empty
.empty))
(.branch 1001 33220
(.branch 1000 10160
.empty
.empty)
(.branch 1002 33236
.empty
.empty)))))))
(.branch 1075 3016
(.branch 1039 10211
(.branch 1021 34675
(.branch 1012 571
(.branch 1008 32987
(.branch 1006 1089
(.branch 1005 1090
(.branch 1004 34611
.empty
.empty)
.empty)
(.branch 1007 34659
.empty
.empty))
(.branch 1010 10396
(.branch 1009 10400
.empty
.empty)
(.branch 1011 32948
.empty
.empty)))
(.branch 1017 10352
(.branch 1015 583
(.branch 1014 34719
(.branch 1013 34723
.empty
.empty)
.empty)
(.branch 1016 32939
.empty
.empty))
(.branch 1019 32996
(.branch 1018 10348
.empty
.empty)
(.branch 1020 568
.empty
.empty))))
(.branch 1030 1085
(.branch 1026 33211
(.branch 1024 10156
(.branch 1023 580
(.branch 1022 34671
.empty
.empty)
.empty)
(.branch 1025 33227
.empty
.empty))
(.branch 1028 34607
(.branch 1027 10204
.empty
.empty)
(.branch 1029 1086
.empty
.empty)))
(.branch 1035 34604
(.branch 1033 1106
(.branch 1032 34652
(.branch 1031 34655
.empty
.empty)
.empty)
(.branch 1034 1105
.empty
.empty))
(.branch 1037 33208
(.branch 1036 10163
.empty
.empty)
(.branch 1038 33224
.empty
.empty)))))
(.branch 1057 1102
(.branch 1048 584
(.branch 1044 32999
(.branch 1042 34672
(.branch 1041 34668
(.branch 1040 587
.empty
.empty)
.empty)
(.branch 1043 599
.empty
.empty))
(.branch 1046 10399
(.branch 1045 10403
.empty
.empty)
(.branch 1047 32936
.empty
.empty)))
(.branch 1053 10355
(.branch 1051 596
(.branch 1050 34720
(.branch 1049 34716
.empty
.empty)
.empty)
(.branch 1052 32951
.empty
.empty))
(.branch 1055 32984
(.branch 1054 10351
.empty
.empty)
(.branch 1056 34656
.empty
.empty))))
(.branch 1066 10133
(.branch 1062 33223
(.branch 1060 10159
(.branch 1059 34608
(.branch 1058 1101
.empty
.empty)
.empty)
(.branch 1061 33239
.empty
.empty))
(.branch 1064 9941
(.branch 1063 10207
.empty
.empty)
(.branch 1065 10090
.empty
.empty)))
(.branch 1071 9294
(.branch 1069 9217
(.branch 1068 9313
(.branch 1067 9946
.empty
.empty)
.empty)
(.branch 1070 9201
.empty
.empty))
(.branch 1073 2887
(.branch 1072 3047
.empty
.empty)
(.branch 1074 2871
.empty
.empty))))))
(.branch 1111 3019
(.branch 1093 9218
(.branch 1084 1290
(.branch 1080 3035
(.branch 1078 1686
(.branch 1077 1641
(.branch 1076 1302
.empty
.empty)
.empty)
(.branch 1079 1305
.empty
.empty))
(.branch 1082 2859
(.branch 1081 2875
.empty
.empty)
(.branch 1083 3028
.empty
.empty)))
(.branch 1089 10089
(.branch 1087 1317
(.branch 1086 1674
(.branch 1085 1653
.empty
.empty)
.empty)
(.branch 1088 9942
.empty
.empty))
(.branch 1091 9945
(.branch 1090 10134
.empty
.empty)
(.branch 1092 9314
.empty
.empty))))
(.branch 1102 10121
(.branch 1098 9197
(.branch 1096 9309
(.branch 1095 9293
(.branch 1094 9202
.empty
.empty)
.empty)
(.branch 1097 9213
.empty
.empty))
(.branch 1100 9929
(.branch 1099 9298
.empty
.empty)
(.branch 1101 10102
.empty
.empty)))
(.branch 1107 1306
(.branch 1105 1642
(.branch 1104 1301
(.branch 1103 9958
.empty
.empty)
.empty)
(.branch 1106 1685
.empty
.empty))
(.branch 1109 2884
(.branch 1108 3044
.empty
.empty)
(.branch 1110 2868
.empty
.empty)))))
(.branch 1129 26979
(.branch 1120 9310
(.branch 1116 3032
(.branch 1114 1673
(.branch 1113 1654
(.branch 1112 1289
.empty
.empty)
.empty)
(.branch 1115 1318
.empty
.empty))
(.branch 1118 2856
(.branch 1117 2872
.empty
.empty)
(.branch 1119 3031
.empty
.empty)))
(.branch 1125 10101
(.branch 1123 9297
(.branch 1122 9198
(.branch 1121 9214
.empty
.empty)
.empty)
(.branch 1124 9930
.empty
.empty))
(.branch 1127 9957
(.branch 1126 10122
.empty
.empty)
(.branch 1128 25383
.empty
.empty))))
(.branch 1138 25557
(.branch 1134 32292
(.branch 1132 30566
(.branch 1131 25359
(.branch 1130 26981
.empty
.empty)
.empty)
(.branch 1133 32290
.empty
.empty))
(.branch 1136 27107
(.branch 1135 30542
.empty
.empty)
(.branch 1137 25555
.empty
.empty)))
(.branch 1142 30484
(.branch 1140 32034
(.branch 1139 27083
.empty
.empty)
(.branch 1141 30482
.empty
.empty))
(.branch 1144 30535
(.branch 1143 32010
.empty
.empty)
(.branch 1145 32259
.empty
.empty))))))))))
(.branch 1719 565
(.branch 1433 53989
(.branch 1290 52662
(.branch 1218 47908
(.branch 1182 25532
(.branch 1164 32036
(.branch 1155 31979
(.branch 1151 25326
(.branch 1149 26946
(.branch 1148 25350
(.branch 1147 30511
.empty
.empty)
.empty)
(.branch 1150 26948
.empty
.empty))
(.branch 1153 30451
(.branch 1152 32003
.empty
.empty)
(.branch 1154 30453
.empty
.empty)))
(.branch 1160 27109
(.branch 1158 25524
(.branch 1157 25522
(.branch 1156 27074
.empty
.empty)
.empty)
(.branch 1159 27050
.empty
.empty))
(.branch 1162 25565
(.branch 1161 25563
.empty
.empty)
(.branch 1163 27085
.empty
.empty))))
(.branch 1173 32266
(.branch 1169 26955
(.branch 1167 32012
(.branch 1166 30492
(.branch 1165 30490
.empty
.empty)
.empty)
(.branch 1168 25377
.empty
.empty))
(.branch 1171 25353
(.branch 1170 26957
.empty
.empty)
(.branch 1172 30560
.empty
.empty)))
(.branch 1178 30461
(.branch 1176 32005
(.branch 1175 30536
(.branch 1174 32268
.empty
.empty)
.empty)
(.branch 1177 30459
.empty
.empty))
(.branch 1180 27076
(.branch 1179 31981
.empty
.empty)
(.branch 1181 25530
.empty
.empty)))))
(.branch 1200 47700
(.branch 1191 25320
(.branch 1187 30505
(.branch 1185 32235
(.branch 1184 30529
(.branch 1183 27052
.empty
.empty)
.empty)
(.branch 1186 32237
.empty
.empty))
(.branch 1189 26922
(.branch 1188 25344
.empty
.empty)
(.branch 1190 26924
.empty
.empty)))
(.branch 1196 48876
(.branch 1194 48692
(.branch 1193 48731
(.branch 1192 25675
.empty
.empty)
.empty)
(.branch 1195 25668
.empty
.empty))
(.branch 1198 26697
(.branch 1197 26694
.empty
.empty)
(.branch 1199 48931
.empty
.empty))))
(.branch 1209 26688
(.branch 1205 47875
(.branch 1203 47675
(.branch 1202 30803
(.branch 1201 30780
.empty
.empty)
.empty)
(.branch 1204 31697
.empty
.empty))
(.branch 1207 31678
(.branch 1206 47884
.empty
.empty)
(.branch 1208 48900
.empty
.empty)))
(.branch 1214 48700
(.branch 1212 25677
(.branch 1211 48907
(.branch 1210 26703
.empty
.empty)
.empty)
(.branch 1213 48723
.empty
.empty))
(.branch 1216 31703
(.branch 1215 25666
.empty
.empty)
(.branch 1217 47851
.empty
.empty))))))
(.branch 1254 48728
(.branch 1236 48904
(.branch 1227 47711
(.branch 1223 47667
(.branch 1221 30778
(.branch 1220 47708
(.branch 1219 31672
.empty
.empty)
.empty)
(.branch 1222 30805
.empty
.empty))
(.branch 1225 30789
(.branch 1224 47664
.empty
.empty)
(.branch 1226 30794
.empty
.empty)))
(.branch 1232 25682
(.branch 1230 47848
(.branch 1229 47911
(.branch 1228 31688
.empty
.empty)
.empty)
(.branch 1231 31687
.empty
.empty))
(.branch 1234 48720
(.branch 1233 48703
.empty
.empty)
(.branch 1235 25661
.empty
.empty))))
(.branch 1245 30787
(.branch 1241 47887
(.branch 1239 48903
(.branch 1238 26704
(.branch 1237 26687
.empty
.empty)
.empty)
(.branch 1240 31694
.empty
.empty))
(.branch 1243 31681
(.branch 1242 47872
.empty
.empty)
(.branch 1244 47672
.empty
.empty)))
(.branch 1250 26710
(.branch 1248 48928
(.branch 1247 47703
(.branch 1246 30796
.empty
.empty)
.empty)
(.branch 1249 26681
.empty
.empty))
(.branch 1252 25684
(.branch 1251 48879
.empty
.empty)
(.branch 1253 48695
.empty
.empty)))))
(.branch 1272 52952
(.branch 1263 53841
(.branch 1259 58854
(.branch 1257 53982
(.branch 1256 60222
(.branch 1255 25659
.empty
.empty)
.empty)
(.branch 1258 52614
.empty
.empty))
(.branch 1261 59001
(.branch 1260 52953
.empty
.empty)
(.branch 1262 59889
.empty
.empty)))
(.branch 1268 60224
(.branch 1266 59887
(.branch 1265 58999
(.branch 1264 52951
.empty
.empty)
.empty)
(.branch 1267 53839
.empty
.empty))
(.branch 1270 52616
(.branch 1269 53984
.empty
.empty)
(.branch 1271 58856
.empty
.empty))))
(.branch 1281 53985
(.branch 1277 53983
(.branch 1275 53840
(.branch 1274 59888
(.branch 1273 59000
.empty
.empty)
.empty)
(.branch 1276 60223
.empty
.empty))
(.branch 1279 58855
(.branch 1278 52615
.empty
.empty)
(.branch 1280 60225
.empty
.empty)))
(.branch 1286 59886
(.branch 1284 52950
(.branch 1283 58857
(.branch 1282 52617
.empty
.empty)
.empty)
(.branch 1285 58998
.empty
.empty))
(.branch 1288 60174
(.branch 1287 53838
.empty
.empty)
(.branch 1289 53934
.empty
.empty)))))))
(.branch 1362 52236
(.branch 1326 54315
(.branch 1308 60175
(.branch 1299 53887
(.branch 1295 53889
(.branch 1293 58953
(.branch 1292 52905
(.branch 1291 58902
.empty
.empty)
.empty)
(.branch 1294 59937
.empty
.empty))
(.branch 1297 58951
(.branch 1296 52903
.empty
.empty)
(.branch 1298 59935
.empty
.empty)))
(.branch 1304 52904
(.branch 1302 52664
(.branch 1301 53936
(.branch 1300 60176
.empty
.empty)
.empty)
(.branch 1303 58904
.empty
.empty))
(.branch 1306 59936
(.branch 1305 58952
.empty
.empty)
(.branch 1307 53888
.empty
.empty))))
(.branch 1317 58950
(.branch 1313 53937
(.branch 1311 58903
(.branch 1310 52663
(.branch 1309 53935
.empty
.empty)
.empty)
(.branch 1312 60177
.empty
.empty))
(.branch 1315 58905
(.branch 1314 52665
.empty
.empty)
(.branch 1316 52902
.empty
.empty)))
(.branch 1322 60314
(.branch 1320 60602
(.branch 1319 53886
(.branch 1318 59934
.empty
.empty)
.empty)
(.branch 1321 58562
.empty
.empty))
(.branch 1324 54219
(.branch 1323 58466
.empty
.empty)
(.branch 1325 52275
.empty
.empty)))))
(.branch 1344 60603
(.branch 1335 58477
(.branch 1331 52572
(.branch 1329 52284
(.branch 1328 54228
(.branch 1327 52563
.empty
.empty)
.empty)
(.branch 1330 54324
.empty
.empty))
(.branch 1333 58573
(.branch 1332 60613
.empty
.empty)
(.branch 1334 60325
.empty
.empty)))
(.branch 1340 60612
(.branch 1338 54325
(.branch 1337 52285
(.branch 1336 54229
.empty
.empty)
.empty)
(.branch 1339 52573
.empty
.empty))
(.branch 1342 60324
(.branch 1341 58572
.empty
.empty)
(.branch 1343 58476
.empty
.empty))))
(.branch 1353 60266
(.branch 1349 52274
(.branch 1347 58467
(.branch 1346 60315
(.branch 1345 58563
.empty
.empty)
.empty)
(.branch 1348 54218
.empty
.empty))
(.branch 1351 52562
(.branch 1350 54314
.empty
.empty)
(.branch 1352 58514
.empty
.empty)))
(.branch 1358 52227
(.branch 1356 52515
(.branch 1355 60554
(.branch 1354 58610
.empty
.empty)
.empty)
(.branch 1357 54363
.empty
.empty))
(.branch 1360 52524
(.branch 1359 54267
.empty
.empty)
(.branch 1361 54372
.empty
.empty))))))
(.branch 1398 59941
(.branch 1380 52514
(.branch 1371 54277
(.branch 1367 60565
(.branch 1365 60277
(.branch 1364 58525
(.branch 1363 54276
.empty
.empty)
.empty)
(.branch 1366 58621
.empty
.empty))
(.branch 1369 54373
(.branch 1368 52525
.empty
.empty)
(.branch 1370 52237
.empty
.empty)))
(.branch 1376 58515
(.branch 1374 58620
(.branch 1373 60276
(.branch 1372 58524
.empty
.empty)
.empty)
(.branch 1375 60564
.empty
.empty))
(.branch 1378 58611
(.branch 1377 60267
.empty
.empty)
(.branch 1379 60555
.empty
.empty))))
(.branch 1389 58995
(.branch 1385 58946
(.branch 1383 54266
(.branch 1382 52226
(.branch 1381 54362
.empty
.empty)
.empty)
(.branch 1384 52898
.empty
.empty))
(.branch 1387 53882
(.branch 1386 59930
.empty
.empty)
(.branch 1388 52947
.empty
.empty)))
(.branch 1394 59892
(.branch 1392 52956
(.branch 1391 53835
(.branch 1390 59883
.empty
.empty)
.empty)
(.branch 1393 59004
.empty
.empty))
(.branch 1396 52909
(.branch 1395 53844
.empty
.empty)
(.branch 1397 58957
.empty
.empty)))))
(.branch 1416 60170
(.branch 1407 53892
(.branch 1403 53845
(.branch 1401 59005
(.branch 1400 52957
(.branch 1399 53893
.empty
.empty)
.empty)
(.branch 1402 59893
.empty
.empty))
(.branch 1405 58956
(.branch 1404 52908
.empty
.empty)
(.branch 1406 59940
.empty
.empty)))
(.branch 1412 52946
(.branch 1410 59931
(.branch 1409 58947
(.branch 1408 52899
.empty
.empty)
.empty)
(.branch 1411 53883
.empty
.empty))
(.branch 1414 59882
(.branch 1413 58994
.empty
.empty)
(.branch 1415 53834
.empty
.empty))))
(.branch 1425 53988
(.branch 1421 53979
(.branch 1419 58898
(.branch 1418 52658
(.branch 1417 53930
.empty
.empty)
.empty)
(.branch 1420 60219
.empty
.empty))
(.branch 1423 58851
(.branch 1422 52611
.empty
.empty)
(.branch 1424 60228
.empty
.empty)))
(.branch 1429 53941
(.branch 1427 58860
(.branch 1426 52620
.empty
.empty)
(.branch 1428 60181
.empty
.empty))
(.branch 1431 58909
(.branch 1430 52669
.empty
.empty)
(.branch 1432 60229
.empty
.empty))))))))
(.branch 1576 25347
(.branch 1505 60273
(.branch 1469 54367
(.branch 1451 54270
(.branch 1442 52659
(.branch 1438 52668
(.branch 1436 60180
(.branch 1435 58861
(.branch 1434 52621
.empty
.empty)
.empty)
(.branch 1437 53940
.empty
.empty))
(.branch 1440 60171
(.branch 1439 58908
.empty
.empty)
(.branch 1441 53931
.empty
.empty)))
(.branch 1447 58850
(.branch 1445 53978
(.branch 1444 60218
(.branch 1443 58899
.empty
.empty)
.empty)
(.branch 1446 52610
.empty
.empty))
(.branch 1449 54366
(.branch 1448 52518
.empty
.empty)
(.branch 1450 52230
.empty
.empty))))
(.branch 1460 52520
(.branch 1456 54223
(.branch 1454 54321
(.branch 1453 52281
(.branch 1452 54225
.empty
.empty)
.empty)
(.branch 1455 52569
.empty
.empty))
(.branch 1458 54319
(.branch 1457 52279
.empty
.empty)
(.branch 1459 52567
.empty
.empty)))
(.branch 1465 52280
(.branch 1463 54272
(.branch 1462 52232
(.branch 1461 54368
.empty
.empty)
.empty)
(.branch 1464 54224
.empty
.empty))
(.branch 1467 52568
(.branch 1466 54320
.empty
.empty)
(.branch 1468 52519
.empty
.empty)))))
(.branch 1487 58473
(.branch 1478 54318
(.branch 1474 52233
(.branch 1472 52521
(.branch 1471 54271
(.branch 1470 52231
.empty
.empty)
.empty)
(.branch 1473 54369
.empty
.empty))
(.branch 1476 54222
(.branch 1475 54273
.empty
.empty)
(.branch 1477 52278
.empty
.empty)))
(.branch 1483 60558
(.branch 1481 60270
(.branch 1480 58518
(.branch 1479 52566
.empty
.empty)
.empty)
(.branch 1482 58614
.empty
.empty))
(.branch 1485 58569
(.branch 1484 60609
.empty
.empty)
(.branch 1486 60321
.empty
.empty))))
(.branch 1496 60608
(.branch 1492 58520
(.branch 1490 60319
(.branch 1489 58567
(.branch 1488 60607
.empty
.empty)
.empty)
(.branch 1491 58471
.empty
.empty))
(.branch 1494 58616
(.branch 1493 60272
.empty
.empty)
(.branch 1495 60560
.empty
.empty)))
(.branch 1501 60271
(.branch 1499 58472
(.branch 1498 60320
(.branch 1497 58568
.empty
.empty)
.empty)
(.branch 1500 58519
.empty
.empty))
(.branch 1503 60559
(.branch 1502 58615
.empty
.empty)
(.branch 1504 58521
.empty
.empty))))))
(.branch 1541 26693
(.branch 1523 48891
(.branch 1514 48740
(.branch 1510 60318
(.branch 1508 60606
(.branch 1507 60561
(.branch 1506 58617
.empty
.empty)
.empty)
(.branch 1509 58566
.empty
.empty))
(.branch 1512 25687
(.branch 1511 58470
.empty
.empty)
(.branch 1513 48683
.empty
.empty)))
(.branch 1519 47663
(.branch 1517 30777
(.branch 1516 47712
(.branch 1515 25656
.empty
.empty)
.empty)
(.branch 1518 30806
.empty
.empty))
(.branch 1521 26684
(.branch 1520 48916
.empty
.empty)
(.branch 1522 26707
.empty
.empty))))
(.branch 1532 25678
(.branch 1528 47684
(.branch 1526 47888
(.branch 1525 47871
(.branch 1524 31698
.empty
.empty)
.empty)
(.branch 1527 31677
.empty
.empty))
(.branch 1530 30799
(.branch 1529 30784
.empty
.empty)
(.branch 1531 47691
.empty
.empty)))
(.branch 1537 47899
(.branch 1535 25665
(.branch 1534 48704
(.branch 1533 48719
.empty
.empty)
.empty)
(.branch 1536 31691
.empty
.empty))
(.branch 1539 31684
(.branch 1538 47860
.empty
.empty)
(.branch 1540 48880
.empty
.empty)))))
(.branch 1559 47687
(.branch 1550 47896
(.branch 1546 26709
(.branch 1544 48924
(.branch 1543 48927
(.branch 1542 26698
.empty
.empty)
.empty)
(.branch 1545 26682
.empty
.empty))
(.branch 1548 31700
(.branch 1547 48883
.empty
.empty)
(.branch 1549 47863
.empty
.empty)))
(.branch 1555 25662
(.branch 1553 48707
(.branch 1552 25681
(.branch 1551 31675
.empty
.empty)
.empty)
(.branch 1554 48716
.empty
.empty))
(.branch 1557 30783
(.branch 1556 47688
.empty
.empty)
(.branch 1558 30800
.empty
.empty))))
(.branch 1568 47660
(.branch 1564 48888
(.branch 1562 47868
(.branch 1561 47891
(.branch 1560 31693
.empty
.empty)
.empty)
(.branch 1563 31682
.empty
.empty))
(.branch 1566 26700
(.branch 1565 26691
.empty
.empty)
(.branch 1567 48919
.empty
.empty)))
(.branch 1572 25672
(.branch 1570 30793
(.branch 1569 30790
.empty
.empty)
(.branch 1571 47715
.empty
.empty))
(.branch 1574 48680
(.branch 1573 48743
.empty
.empty)
(.branch 1575 25671
.empty
.empty)))))))
(.branch 1648 9307
(.branch 1612 32000
(.branch 1594 25541
(.branch 1585 32275
(.branch 1581 25515
(.branch 1579 25323
(.branch 1578 26933
(.branch 1577 26931
.empty
.empty)
.empty)
(.branch 1580 27073
.empty
.empty))
(.branch 1583 27049
(.branch 1582 25517
.empty
.empty)
(.branch 1584 30563
.empty
.empty)))
(.branch 1590 30477
(.branch 1588 32033
(.branch 1587 30539
(.branch 1586 32277
.empty
.empty)
.empty)
(.branch 1589 30475
.empty
.empty))
(.branch 1592 27079
(.branch 1591 32009
.empty
.empty)
(.branch 1593 25539
.empty
.empty))))
(.branch 1603 32015
(.branch 1599 25325
(.branch 1597 26939
(.branch 1596 25349
(.branch 1595 27055
.empty
.empty)
.empty)
(.branch 1598 26941
.empty
.empty))
(.branch 1601 30499
(.branch 1600 32039
.empty
.empty)
(.branch 1602 30501
.empty
.empty)))
(.branch 1608 30530
(.branch 1606 32285
(.branch 1605 32283
(.branch 1604 30565
.empty
.empty)
.empty)
(.branch 1607 30541
.empty
.empty))
(.branch 1610 32244
(.branch 1609 32242
.empty
.empty)
(.branch 1611 30506
.empty
.empty)))))
(.branch 1630 32252
(.branch 1621 25546
(.branch 1617 26962
(.branch 1615 31976
(.branch 1614 30444
(.branch 1613 30442
.empty
.empty)
.empty)
(.branch 1616 25378
.empty
.empty))
(.branch 1619 25354
(.branch 1618 26964
.empty
.empty)
(.branch 1620 27104
.empty
.empty)))
(.branch 1626 30468
(.branch 1624 32006
(.branch 1623 27080
(.branch 1622 25548
.empty
.empty)
.empty)
(.branch 1625 30466
.empty
.empty))
(.branch 1628 30532
(.branch 1627 31982
.empty
.empty)
(.branch 1629 32250
.empty
.empty))))
(.branch 1639 25356
(.branch 1635 27086
(.branch 1633 25570
(.branch 1632 27110
(.branch 1631 30508
.empty
.empty)
.empty)
(.branch 1634 25572
.empty
.empty))
(.branch 1637 26970
(.branch 1636 25380
.empty
.empty)
(.branch 1638 26972
.empty
.empty)))
(.branch 1644 3041
(.branch 1642 10127
(.branch 1641 10096
(.branch 1640 9935
.empty
.empty)
.empty)
(.branch 1643 9952
.empty
.empty))
(.branch 1646 2865
(.branch 1645 2881
.empty
.empty)
(.branch 1647 3022
.empty
.empty))))))
(.branch 1684 9304
(.branch 1666 10131
(.branch 1657 9223
(.branch 1653 1647
(.branch 1651 9300
(.branch 1650 9195
(.branch 1649 9211
.empty
.empty)
.empty)
(.branch 1652 1296
.empty
.empty))
(.branch 1655 1311
(.branch 1654 1680
.empty
.empty)
(.branch 1656 9319
.empty
.empty)))
(.branch 1662 1683
(.branch 1660 1299
(.branch 1659 9288
(.branch 1658 9207
.empty
.empty)
.empty)
(.branch 1661 1644
.empty
.empty))
(.branch 1664 9939
(.branch 1663 1308
.empty
.empty)
(.branch 1665 10092
.empty
.empty))))
(.branch 1675 3026
(.branch 1671 3021
(.branch 1669 2882
(.branch 1668 3042
(.branch 1667 9948
.empty
.empty)
.empty)
(.branch 1670 2866
.empty
.empty))
(.branch 1673 2877
(.branch 1672 3037
.empty
.empty)
(.branch 1674 2861
.empty
.empty)))
(.branch 1680 1292
(.branch 1678 10124
(.branch 1677 10099
(.branch 1676 9932
.empty
.empty)
.empty)
(.branch 1679 9955
.empty
.empty))
(.branch 1682 1676
(.branch 1681 1651
.empty
.empty)
(.branch 1683 1315
.empty
.empty)))))
(.branch 1702 10128
(.branch 1693 9220
(.branch 1689 1648
(.branch 1687 9303
(.branch 1686 9192
(.branch 1685 9208
.empty
.empty)
.empty)
(.branch 1688 1295
.empty
.empty))
(.branch 1691 1312
(.branch 1690 1679
.empty
.empty)
(.branch 1692 9316
.empty
.empty)))
(.branch 1698 2862
(.branch 1696 3038
(.branch 1695 9291
(.branch 1694 9204
.empty
.empty)
.empty)
(.branch 1697 2878
.empty
.empty))
(.branch 1700 9936
(.branch 1699 3025
.empty
.empty)
(.branch 1701 10095
.empty
.empty))))
(.branch 1711 32972
(.branch 1707 10202
(.branch 1705 33235
(.branch 1704 10154
(.branch 1703 9951
.empty
.empty)
.empty)
(.branch 1706 33219
.empty
.empty))
(.branch 1709 10370
(.branch 1708 32963
.empty
.empty)
(.branch 1710 10366
.empty
.empty)))
(.branch 1715 34651
(.branch 1713 1066
(.branch 1712 34603
.empty
.empty)
(.branch 1714 1065
.empty
.empty))
(.branch 1717 34691
(.branch 1716 553
.empty
.empty)
(.branch 1718 34687
.empty
.empty)))))))))
(.branch 2006 92647
(.branch 1863 33684
(.branch 1791 10241
(.branch 1755 614
(.branch 1737 10386
(.branch 1728 10153
(.branch 1724 601
(.branch 1722 1113
(.branch 1721 1114
(.branch 1720 34660
.empty
.empty)
.empty)
(.branch 1723 34612
.empty
.empty))
(.branch 1726 34704
(.branch 1725 34700
.empty
.empty)
(.branch 1727 613
.empty
.empty)))
(.branch 1733 10369
(.branch 1731 10201
(.branch 1730 33215
(.branch 1729 33231
.empty
.empty)
.empty)
(.branch 1732 32959
.empty
.empty))
(.branch 1735 32976
(.branch 1734 10365
.empty
.empty)
(.branch 1736 32979
.empty
.empty))))
(.branch 1746 34703
(.branch 1742 33228
(.branch 1740 10166
(.branch 1739 32956
(.branch 1738 10382
.empty
.empty)
.empty)
(.branch 1741 33212
.empty
.empty))
(.branch 1744 554
(.branch 1743 10214
.empty
.empty)
(.branch 1745 34707
.empty
.empty)))
(.branch 1751 34663
(.branch 1749 1078
(.branch 1748 34615
(.branch 1747 566
.empty
.empty)
.empty)
(.branch 1750 1077
.empty
.empty))
(.branch 1753 34684
(.branch 1752 602
.empty
.empty)
(.branch 1754 34688
.empty
.empty)))))
(.branch 1773 10240
(.branch 1764 10165
(.branch 1760 32975
(.branch 1758 1125
(.branch 1757 1126
(.branch 1756 34648
.empty
.empty)
.empty)
(.branch 1759 34600
.empty
.empty))
(.branch 1762 10381
(.branch 1761 10385
.empty
.empty)
(.branch 1763 32960
.empty
.empty)))
(.branch 1769 327
(.branch 1767 10213
(.branch 1766 33232
(.branch 1765 33216
.empty
.empty)
.empty)
(.branch 1768 324
.empty
.empty))
(.branch 1771 10242
(.branch 1770 10218
.empty
.empty)
(.branch 1772 10216
.empty
.empty))))
(.branch 1782 421
(.branch 1778 10266
(.branch 1776 325
(.branch 1775 450
(.branch 1774 405
.empty
.empty)
.empty)
(.branch 1777 50
.empty
.empty))
(.branch 1780 10264
(.branch 1779 10238
.empty
.empty)
(.branch 1781 10236
.empty
.empty)))
(.branch 1787 173
(.branch 1785 10255
(.branch 1784 10279
(.branch 1783 160
.empty
.empty)
.empty)
(.branch 1786 128
.empty
.empty))
(.branch 1789 347
(.branch 1788 344
.empty
.empty)
(.branch 1790 10217
.empty
.empty))))))
(.branch 1827 404
(.branch 1809 48
(.branch 1800 326
(.branch 1796 345
(.branch 1794 144
(.branch 1793 10259
(.branch 1792 10231
.empty
.empty)
.empty)
(.branch 1795 435
.empty
.empty))
(.branch 1798 10265
(.branch 1797 70
.empty
.empty)
(.branch 1799 10237
.empty
.empty)))
(.branch 1805 10228
(.branch 1803 10230
(.branch 1802 10258
(.branch 1801 49
.empty
.empty)
.empty)
(.branch 1804 10256
.empty
.empty))
(.branch 1807 145
(.branch 1806 436
.empty
.empty)
(.branch 1808 51
.empty
.empty))))
(.branch 1818 159
(.branch 1814 174
(.branch 1812 10252
(.branch 1811 10278
(.branch 1810 10254
.empty
.empty)
.empty)
(.branch 1813 10276
.empty
.empty))
(.branch 1816 10239
(.branch 1815 129
.empty
.empty)
(.branch 1817 10267
.empty
.empty)))
(.branch 1823 10229
(.branch 1821 69
(.branch 1820 346
(.branch 1819 420
.empty
.empty)
.empty)
(.branch 1822 10257
.empty
.empty))
(.branch 1825 10219
(.branch 1824 10243
.empty
.empty)
(.branch 1826 449
.empty
.empty)))))
(.branch 1845 34524
(.branch 1836 33591
(.branch 1832 1235
(.branch 1830 10253
(.branch 1829 68
(.branch 1828 71
.empty
.empty)
.empty)
(.branch 1831 10277
.empty
.empty))
(.branch 1834 34511
(.branch 1833 33607
.empty
.empty)
(.branch 1835 3073
.empty
.empty)))
(.branch 1841 3074
(.branch 1839 34528
(.branch 1838 3057
(.branch 1837 1244
.empty
.empty)
.empty)
(.branch 1840 34515
.empty
.empty))
(.branch 1843 33595
(.branch 1842 1232
.empty
.empty)
(.branch 1844 3058
.empty
.empty))))
(.branch 1854 34319
(.branch 1850 2977
(.branch 1848 33703
(.branch 1847 1247
(.branch 1846 33579
.empty
.empty)
.empty)
(.branch 1849 1580
.empty
.empty))
(.branch 1852 1619
(.branch 1851 34288
.empty
.empty)
(.branch 1853 33672
.empty
.empty)))
(.branch 1859 1583
(.branch 1857 34284
(.branch 1856 2978
(.branch 1855 2958
.empty
.empty)
.empty)
(.branch 1858 33691
.empty
.empty))
(.branch 1861 2957
(.branch 1860 34323
.empty
.empty)
(.branch 1862 1616
.empty
.empty)))))))
(.branch 1935 94068
(.branch 1899 86066
(.branch 1881 1584
(.branch 1872 34512
(.branch 1868 33588
(.branch 1866 34508
(.branch 1865 33604
(.branch 1864 1231
.empty
.empty)
.empty)
(.branch 1867 3069
.empty
.empty))
(.branch 1870 3053
(.branch 1869 1248
.empty
.empty)
(.branch 1871 34531
.empty
.empty)))
(.branch 1877 34527
(.branch 1875 33592
(.branch 1874 1228
(.branch 1873 3070
.empty
.empty)
.empty)
(.branch 1876 3054
.empty
.empty))
(.branch 1879 1251
(.branch 1878 33576
.empty
.empty)
(.branch 1880 33700
.empty
.empty))))
(.branch 1890 33688
(.branch 1886 34316
(.branch 1884 1615
(.branch 1883 34291
(.branch 1882 2973
.empty
.empty)
.empty)
(.branch 1885 33675
.empty
.empty))
(.branch 1888 2974
(.branch 1887 2962
.empty
.empty)
(.branch 1889 34287
.empty
.empty)))
(.branch 1895 33687
(.branch 1893 2961
(.branch 1892 34320
(.branch 1891 1587
.empty
.empty)
.empty)
(.branch 1894 1612
.empty
.empty))
(.branch 1897 94346
(.branch 1896 88106
.empty
.empty)
(.branch 1898 92306
.empty
.empty)))))
(.branch 1917 86355
(.branch 1908 92413
(.branch 1904 88165
(.branch 1902 88058
(.branch 1901 86306
(.branch 1900 92354
.empty
.empty)
.empty)
(.branch 1903 94106
.empty
.empty))
(.branch 1906 92269
(.branch 1905 94405
.empty
.empty)
(.branch 1907 86029
.empty
.empty)))
(.branch 1913 94395
(.branch 1911 94069
(.branch 1910 88021
(.branch 1909 86365
.empty
.empty)
.empty)
(.branch 1912 88155
.empty
.empty))
(.branch 1915 86019
(.branch 1914 92259
.empty
.empty)
(.branch 1916 92403
.empty
.empty))))
(.branch 1926 88068
(.branch 1922 92316
(.branch 1920 88116
(.branch 1919 94059
(.branch 1918 88011
.empty
.empty)
.empty)
(.branch 1921 94356
.empty
.empty))
(.branch 1924 92364
(.branch 1923 86076
.empty
.empty)
(.branch 1925 86316
.empty
.empty)))
(.branch 1931 86028
(.branch 1929 94404
(.branch 1928 88164
(.branch 1927 94116
.empty
.empty)
.empty)
(.branch 1930 92268
.empty
.empty))
(.branch 1933 86364
(.branch 1932 92412
.empty
.empty)
(.branch 1934 88020
.empty
.empty))))))
(.branch 1971 87776
(.branch 1953 94394
(.branch 1944 88117
(.branch 1940 92355
(.branch 1938 92307
(.branch 1937 94347
(.branch 1936 88107
.empty
.empty)
.empty)
(.branch 1939 86067
.empty
.empty))
(.branch 1942 88059
(.branch 1941 86307
.empty
.empty)
(.branch 1943 94107
.empty
.empty)))
(.branch 1949 86317
(.branch 1947 86077
(.branch 1946 92317
(.branch 1945 94357
.empty
.empty)
.empty)
(.branch 1948 92365
.empty
.empty))
(.branch 1951 94117
(.branch 1950 88069
.empty
.empty)
(.branch 1952 88154
.empty
.empty))))
(.branch 1962 86742
(.branch 1958 88010
(.branch 1956 92402
(.branch 1955 86018
(.branch 1954 92258
.empty
.empty)
.empty)
(.branch 1957 86354
.empty
.empty))
(.branch 1960 87726
(.branch 1959 94058
.empty
.empty)
(.branch 1961 87630
.empty
.empty)))
(.branch 1967 92742
(.branch 1965 94014
(.branch 1964 93726
(.branch 1963 86454
.empty
.empty)
.empty)
(.branch 1966 92646
.empty
.empty))
(.branch 1969 86696
(.branch 1968 86408
.empty
.empty)
(.branch 1970 87680
.empty
.empty)))))
(.branch 1989 94017
(.branch 1980 92791
(.branch 1976 86407
(.branch 1974 93968
(.branch 1973 92696
(.branch 1972 92792
.empty
.empty)
.empty)
(.branch 1975 93680
.empty
.empty))
(.branch 1978 87679
(.branch 1977 86695
.empty
.empty)
(.branch 1979 87775
.empty
.empty)))
(.branch 1985 87633
(.branch 1983 93679
(.branch 1982 93967
(.branch 1981 92695
.empty
.empty)
.empty)
(.branch 1984 87729
.empty
.empty))
(.branch 1987 86457
(.branch 1986 86745
.empty
.empty)
(.branch 1988 93729
.empty
.empty))))
(.branch 1998 93969
(.branch 1994 87681
(.branch 1992 86409
(.branch 1991 92745
(.branch 1990 92649
.empty
.empty)
.empty)
(.branch 1993 86697
.empty
.empty))
(.branch 1996 92793
(.branch 1995 87777
.empty
.empty)
(.branch 1997 92697
.empty
.empty)))
(.branch 2002 86743
(.branch 2000 87727
(.branch 1999 93681
.empty
.empty)
(.branch 2001 87631
.empty
.empty))
(.branch 2004 93727
(.branch 2003 86455
.empty
.empty)
(.branch 2005 94015
.empty
.empty))))))))
(.branch 2149 58874
(.branch 2078 60630
(.branch 2042 60633
(.branch 2024 60294
(.branch 2015 92744
(.branch 2011 86456
(.branch 2009 87632
(.branch 2008 87728
(.branch 2007 92743
.empty
.empty)
.empty)
(.branch 2010 86744
.empty
.empty))
(.branch 2013 94016
(.branch 2012 93728
.empty
.empty)
(.branch 2014 92648
.empty
.empty)))
(.branch 2020 92790
(.branch 2018 87678
(.branch 2017 86694
(.branch 2016 86406
.empty
.empty)
.empty)
(.branch 2019 87774
.empty
.empty))
(.branch 2022 93966
(.branch 2021 92694
.empty
.empty)
(.branch 2023 93678
.empty
.empty))))
(.branch 2033 54294
(.branch 2029 58448
(.branch 2027 58590
(.branch 2026 58494
(.branch 2025 60582
.empty
.empty)
.empty)
(.branch 2028 58544
.empty
.empty))
(.branch 2031 60344
(.branch 2030 60632
.empty
.empty)
(.branch 2032 54390
.empty
.empty)))
(.branch 2038 54248
(.branch 2036 52256
(.branch 2035 52206
(.branch 2034 52494
.empty
.empty)
.empty)
(.branch 2037 52544
.empty
.empty))
(.branch 2040 58545
(.branch 2039 54344
.empty
.empty)
(.branch 2041 58449
.empty
.empty)))))
(.branch 2060 60297
(.branch 2051 54345
(.branch 2047 58591
(.branch 2045 60583
(.branch 2044 60295
(.branch 2043 60345
.empty
.empty)
.empty)
(.branch 2046 58495
.empty
.empty))
(.branch 2049 52545
(.branch 2048 52257
.empty
.empty)
(.branch 2050 54249
.empty
.empty)))
(.branch 2056 58543
(.branch 2054 52495
(.branch 2053 54295
(.branch 2052 54391
.empty
.empty)
.empty)
(.branch 2055 52207
.empty
.empty))
(.branch 2058 60631
(.branch 2057 58447
.empty
.empty)
(.branch 2059 60343
.empty
.empty))))
(.branch 2069 54297
(.branch 2065 52543
(.branch 2063 58593
(.branch 2062 58497
(.branch 2061 60585
.empty
.empty)
.empty)
(.branch 2064 52255
.empty
.empty))
(.branch 2067 54343
(.branch 2066 54247
.empty
.empty)
(.branch 2068 54393
.empty
.empty)))
(.branch 2074 58496
(.branch 2072 60296
(.branch 2071 52209
(.branch 2070 52497
.empty
.empty)
.empty)
(.branch 2073 60584
.empty
.empty))
(.branch 2076 58542
(.branch 2075 58592
.empty
.empty)
(.branch 2077 58446
.empty
.empty))))))
(.branch 2114 60204
(.branch 2096 52586
(.branch 2087 54342
(.branch 2083 52208
(.branch 2081 54296
(.branch 2080 54392
(.branch 2079 60342
.empty
.empty)
.empty)
(.branch 2082 52496
.empty
.empty))
(.branch 2085 52542
(.branch 2084 52254
.empty
.empty)
(.branch 2086 54246
.empty
.empty)))
(.branch 2092 59965
(.branch 2090 52922
(.branch 2089 53858
(.branch 2088 59906
.empty
.empty)
.empty)
(.branch 2091 58970
.empty
.empty))
(.branch 2094 52885
(.branch 2093 53917
.empty
.empty)
(.branch 2095 58933
.empty
.empty))))
(.branch 2105 53916
(.branch 2101 58885
(.branch 2099 54002
(.branch 2098 60242
(.branch 2097 58826
.empty
.empty)
.empty)
(.branch 2100 52645
.empty
.empty))
(.branch 2103 53965
(.branch 2102 60205
.empty
.empty)
(.branch 2104 59964
.empty
.empty)))
(.branch 2110 52923
(.branch 2108 59907
(.branch 2107 58932
(.branch 2106 52884
.empty
.empty)
.empty)
(.branch 2109 53859
.empty
.empty))
(.branch 2112 52644
(.branch 2111 58971
.empty
.empty)
(.branch 2113 58884
.empty
.empty)))))
(.branch 2132 52596
(.branch 2123 58923
(.branch 2119 54003
(.branch 2117 58827
(.branch 2116 52587
(.branch 2115 53964
.empty
.empty)
.empty)
(.branch 2118 60243
.empty
.empty))
(.branch 2121 53907
(.branch 2120 59955
.empty
.empty)
(.branch 2122 52875
.empty
.empty)))
(.branch 2128 52635
(.branch 2126 52932
(.branch 2125 53868
(.branch 2124 59916
.empty
.empty)
.empty)
(.branch 2127 58980
.empty
.empty))
(.branch 2130 60195
(.branch 2129 58875
.empty
.empty)
(.branch 2131 53955
.empty
.empty))))
(.branch 2141 53906
(.branch 2137 53869
(.branch 2135 54012
(.branch 2134 60252
(.branch 2133 58836
.empty
.empty)
.empty)
(.branch 2136 59917
.empty
.empty))
(.branch 2139 58981
(.branch 2138 52933
.empty
.empty)
(.branch 2140 59954
.empty
.empty)))
(.branch 2145 58837
(.branch 2143 58922
(.branch 2142 52874
.empty
.empty)
(.branch 2144 52597
.empty
.empty))
(.branch 2147 54013
(.branch 2146 60253
.empty
.empty)
(.branch 2148 52634
.empty
.empty)))))))
(.branch 2221 94010
(.branch 2185 94401
(.branch 2167 86072
(.branch 2158 88062
(.branch 2154 88014
(.branch 2152 92406
(.branch 2151 53954
(.branch 2150 60194
.empty
.empty)
.empty)
(.branch 2153 86358
.empty
.empty))
(.branch 2156 92358
(.branch 2155 94062
.empty
.empty)
(.branch 2157 86310
.empty
.empty)))
(.branch 2163 86024
(.branch 2161 94400
(.branch 2160 88160
(.branch 2159 94110
.empty
.empty)
.empty)
(.branch 2162 92264
.empty
.empty))
(.branch 2165 94352
(.branch 2164 88112
.empty
.empty)
(.branch 2166 92312
.empty
.empty))))
(.branch 2176 92409
(.branch 2172 88111
(.branch 2170 92263
(.branch 2169 94399
(.branch 2168 88159
.empty
.empty)
.empty)
(.branch 2171 86023
.empty
.empty))
(.branch 2174 92311
(.branch 2173 94351
.empty
.empty)
(.branch 2175 86071
.empty
.empty)))
(.branch 2181 86313
(.branch 2179 94065
(.branch 2178 88017
(.branch 2177 86361
.empty
.empty)
.empty)
(.branch 2180 92361
.empty
.empty))
(.branch 2183 94113
(.branch 2182 88065
.empty
.empty)
(.branch 2184 88161
.empty
.empty)))))
(.branch 2203 94064
(.branch 2194 88015
(.branch 2190 92313
(.branch 2188 88113
(.branch 2187 86025
(.branch 2186 92265
.empty
.empty)
.empty)
(.branch 2189 94353
.empty
.empty))
(.branch 2192 92407
(.branch 2191 86073
.empty
.empty)
(.branch 2193 86359
.empty
.empty)))
(.branch 2199 94111
(.branch 2197 86311
(.branch 2196 92359
(.branch 2195 94063
.empty
.empty)
.empty)
(.branch 2198 88063
.empty
.empty))
(.branch 2201 86360
(.branch 2200 92408
.empty
.empty)
(.branch 2202 88016
.empty
.empty))))
(.branch 2212 88110
(.branch 2208 88158
(.branch 2206 88064
(.branch 2205 86312
(.branch 2204 92360
.empty
.empty)
.empty)
(.branch 2207 94112
.empty
.empty))
(.branch 2210 92262
(.branch 2209 94398
.empty
.empty)
(.branch 2211 86022
.empty
.empty)))
(.branch 2217 92690
(.branch 2215 86070
(.branch 2214 92310
(.branch 2213 94350
.empty
.empty)
.empty)
(.branch 2216 92786
.empty
.empty))
(.branch 2219 93674
(.branch 2218 93962
.empty
.empty)
(.branch 2220 93722
.empty
.empty))))))
(.branch 2257 92691
(.branch 2239 86451
(.branch 2230 86749
(.branch 2226 87685
(.branch 2224 86413
(.branch 2223 92738
(.branch 2222 92642
.empty
.empty)
.empty)
(.branch 2225 86701
.empty
.empty))
(.branch 2228 87733
(.branch 2227 87781
.empty
.empty)
(.branch 2229 87637
.empty
.empty)))
(.branch 2235 87771
(.branch 2233 86691
(.branch 2232 86403
(.branch 2231 86461
.empty
.empty)
.empty)
(.branch 2234 87675
.empty
.empty))
(.branch 2237 87627
(.branch 2236 87723
.empty
.empty)
(.branch 2238 86739
.empty
.empty))))
(.branch 2248 86412
(.branch 2244 93732
(.branch 2242 93972
(.branch 2241 92700
(.branch 2240 92796
.empty
.empty)
.empty)
(.branch 2243 93684
.empty
.empty))
(.branch 2246 92652
(.branch 2245 94020
.empty
.empty)
(.branch 2247 92748
.empty
.empty)))
(.branch 2253 87636
(.branch 2251 87780
(.branch 2250 87684
(.branch 2249 86700
.empty
.empty)
.empty)
(.branch 2252 87732
.empty
.empty))
(.branch 2255 86460
(.branch 2254 86748
.empty
.empty)
(.branch 2256 92787
.empty
.empty)))))
(.branch 2275 87770
(.branch 2266 93973
(.branch 2262 92643
(.branch 2260 93723
(.branch 2259 93675
(.branch 2258 93963
.empty
.empty)
.empty)
(.branch 2261 94011
.empty
.empty))
(.branch 2264 92797
(.branch 2263 92739
.empty
.empty)
(.branch 2265 92701
.empty
.empty)))
(.branch 2271 92749
(.branch 2269 94021
(.branch 2268 93733
(.branch 2267 93685
.empty
.empty)
.empty)
(.branch 2270 92653
.empty
.empty))
(.branch 2273 86690
(.branch 2272 86402
.empty
.empty)
(.branch 2274 87674
.empty
.empty))))
(.branch 2284 58549
(.branch 2280 52250
(.branch 2278 86738
(.branch 2277 87626
(.branch 2276 87722
.empty
.empty)
.empty)
(.branch 2279 86450
.empty
.empty))
(.branch 2282 54242
(.branch 2281 52538
.empty
.empty)
(.branch 2283 54338
.empty
.empty)))
(.branch 2288 54386
(.branch 2286 60637
(.branch 2285 58453
.empty
.empty)
(.branch 2287 60349
.empty
.empty))
(.branch 2290 52490
(.branch 2289 54290
.empty
.empty)
(.branch 2291 52202
.empty
.empty)))))))))))
(.branch 3438 47602
(.branch 2865 58993
(.branch 2579 93673
(.branch 2436 47971
(.branch 2364 52639
(.branch 2328 52261
(.branch 2310 52491
(.branch 2301 52539
(.branch 2297 58452
(.branch 2295 58597
(.branch 2294 58501
(.branch 2293 60589
.empty
.empty)
.empty)
(.branch 2296 58548
.empty
.empty))
(.branch 2299 60348
(.branch 2298 60636
.empty
.empty)
(.branch 2300 52251
.empty
.empty)))
(.branch 2306 58500
(.branch 2304 60300
(.branch 2303 54339
(.branch 2302 54243
.empty
.empty)
.empty)
(.branch 2305 60588
.empty
.empty))
(.branch 2308 54387
(.branch 2307 58596
.empty
.empty)
(.branch 2309 54291
.empty
.empty))))
(.branch 2319 54348
(.branch 2315 60339
(.branch 2313 58443
(.branch 2312 58539
(.branch 2311 52203
.empty
.empty)
.empty)
(.branch 2314 60627
.empty
.empty))
(.branch 2317 52548
(.branch 2316 52260
.empty
.empty)
(.branch 2318 54252
.empty
.empty)))
(.branch 2324 54396
(.branch 2322 58491
(.branch 2321 60579
(.branch 2320 60291
.empty
.empty)
.empty)
(.branch 2323 58587
.empty
.empty))
(.branch 2326 52500
(.branch 2325 54300
.empty
.empty)
(.branch 2327 52212
.empty
.empty)))))
(.branch 2346 60198
(.branch 2337 54301
(.branch 2333 58442
(.branch 2331 54349
(.branch 2330 54253
(.branch 2329 52549
.empty
.empty)
.empty)
(.branch 2332 58538
.empty
.empty))
(.branch 2335 60338
(.branch 2334 60626
.empty
.empty)
(.branch 2336 54397
.empty
.empty)))
(.branch 2342 58490
(.branch 2340 60290
(.branch 2339 52213
(.branch 2338 52501
.empty
.empty)
.empty)
(.branch 2341 60578
.empty
.empty))
(.branch 2344 52638
(.branch 2343 58586
.empty
.empty)
(.branch 2345 58878
.empty
.empty))))
(.branch 2355 54006
(.branch 2351 58928
(.branch 2349 53912
(.branch 2348 59960
(.branch 2347 53958
.empty
.empty)
.empty)
(.branch 2350 52880
.empty
.empty))
(.branch 2353 58830
(.branch 2352 52590
.empty
.empty)
(.branch 2354 60246
.empty
.empty)))
(.branch 2360 59961
(.branch 2358 52928
(.branch 2357 53864
(.branch 2356 59912
.empty
.empty)
.empty)
(.branch 2359 58976
.empty
.empty))
(.branch 2362 52881
(.branch 2361 53913
.empty
.empty)
(.branch 2363 58929
.empty
.empty))))))
(.branch 2400 52592
(.branch 2382 60201
(.branch 2373 58831
(.branch 2369 53865
(.branch 2367 53959
(.branch 2366 60199
(.branch 2365 58879
.empty
.empty)
.empty)
(.branch 2368 59913
.empty
.empty))
(.branch 2371 58977
(.branch 2370 52929
.empty
.empty)
(.branch 2372 52591
.empty
.empty)))
(.branch 2378 52879
(.branch 2376 59959
(.branch 2375 54007
(.branch 2374 60247
.empty
.empty)
.empty)
(.branch 2377 53911
.empty
.empty))
(.branch 2380 52641
(.branch 2379 58927
.empty
.empty)
(.branch 2381 58881
.empty
.empty))))
(.branch 2391 54009
(.branch 2387 58975
(.branch 2385 53863
(.branch 2384 59911
(.branch 2383 53961
.empty
.empty)
.empty)
(.branch 2386 52927
.empty
.empty))
(.branch 2389 58833
(.branch 2388 52593
.empty
.empty)
(.branch 2390 60249
.empty
.empty)))
(.branch 2396 59958
(.branch 2394 60200
(.branch 2393 58880
(.branch 2392 52640
.empty
.empty)
.empty)
(.branch 2395 53960
.empty
.empty))
(.branch 2398 52878
(.branch 2397 53910
.empty
.empty)
(.branch 2399 58926
.empty
.empty)))))
(.branch 2418 32080
(.branch 2409 47607
(.branch 2405 53862
(.branch 2403 54008
(.branch 2402 60248
(.branch 2401 58832
.empty
.empty)
.empty)
(.branch 2404 59910
.empty
.empty))
(.branch 2407 58974
(.branch 2406 52926
.empty
.empty)
(.branch 2408 25299
.empty
.empty)))
(.branch 2414 25301
(.branch 2412 48999
(.branch 2411 32073
(.branch 2410 48975
.empty
.empty)
.empty)
(.branch 2413 32079
.empty
.empty))
(.branch 2416 47635
(.branch 2415 47615
.empty
.empty)
(.branch 2417 25290
.empty
.empty))))
(.branch 2427 47919
(.branch 2423 25292
(.branch 2421 48963
(.branch 2420 32086
(.branch 2419 48939
.empty
.empty)
.empty)
(.branch 2422 47643
.empty
.empty))
(.branch 2425 30603
(.branch 2424 48663
.empty
.empty)
(.branch 2426 27025
.empty
.empty)))
(.branch 2432 30610
(.branch 2430 48671
(.branch 2429 47943
(.branch 2428 27031
.empty
.empty)
.empty)
(.branch 2431 30605
.empty
.empty))
(.branch 2434 47947
(.branch 2433 48627
.empty
.empty)
(.branch 2435 27016
.empty
.empty)))))))
(.branch 2508 30854
(.branch 2472 25607
(.branch 2454 47640
(.branch 2445 32063
(.branch 2441 47604
(.branch 2439 48635
(.branch 2438 30612
(.branch 2437 27022
.empty
.empty)
.empty)
(.branch 2440 25283
.empty
.empty))
(.branch 2443 32057
(.branch 2442 48972
.empty
.empty)
(.branch 2444 48996
.empty
.empty)))
(.branch 2450 32064
(.branch 2448 47632
(.branch 2447 47612
(.branch 2446 25285
.empty
.empty)
.empty)
(.branch 2449 25274
.empty
.empty))
(.branch 2452 32070
(.branch 2451 48936
.empty
.empty)
(.branch 2453 48960
.empty
.empty))))
(.branch 2463 30589
(.branch 2459 47916
(.branch 2457 30587
(.branch 2456 48660
(.branch 2455 25276
.empty
.empty)
.empty)
(.branch 2458 27009
.empty
.empty))
(.branch 2461 47940
(.branch 2460 27015
.empty
.empty)
(.branch 2462 48668
.empty
.empty)))
(.branch 2468 47968
(.branch 2466 47944
(.branch 2465 48624
(.branch 2464 30594
.empty
.empty)
.empty)
(.branch 2467 27000
.empty
.empty))
(.branch 2470 30596
(.branch 2469 27006
.empty
.empty)
(.branch 2471 48632
.empty
.empty)))))
(.branch 2490 25851
(.branch 2481 26762
(.branch 2477 25608
(.branch 2475 26764
(.branch 2474 31971
(.branch 2473 30824
.empty
.empty)
.empty)
(.branch 2476 30887
.empty
.empty))
(.branch 2479 31916
(.branch 2478 26755
.empty
.empty)
(.branch 2480 31973
.empty
.empty)))
(.branch 2486 30863
(.branch 2484 26757
(.branch 2483 30848
(.branch 2482 25583
.empty
.empty)
.empty)
(.branch 2485 31914
.empty
.empty))
(.branch 2488 31781
(.branch 2487 25632
.empty
.empty)
(.branch 2489 26634
.empty
.empty))))
(.branch 2499 26658
(.branch 2495 25876
(.branch 2493 31722
(.branch 2492 26629
(.branch 2491 30900
.empty
.empty)
.empty)
(.branch 2494 30939
.empty
.empty))
(.branch 2497 30898
(.branch 2496 25853
.empty
.empty)
(.branch 2498 31757
.empty
.empty)))
(.branch 2504 25638
(.branch 2502 26605
(.branch 2501 25874
(.branch 2500 30941
.empty
.empty)
.empty)
(.branch 2503 31746
.empty
.empty))
(.branch 2506 31938
(.branch 2505 30857
.empty
.empty)
(.branch 2507 26733
.empty
.empty))))))
(.branch 2544 86401
(.branch 2526 30906
(.branch 2517 31947
(.branch 2513 26731
(.branch 2511 31949
(.branch 2510 26786
(.branch 2509 25577
.empty
.empty)
.empty)
(.branch 2512 31940
.empty
.empty))
(.branch 2515 30881
(.branch 2514 25614
.empty
.empty)
(.branch 2516 26788
.empty
.empty)))
(.branch 2522 25882
(.branch 2520 31748
(.branch 2519 25601
(.branch 2518 30830
.empty
.empty)
.empty)
(.branch 2521 26603
.empty
.empty))
(.branch 2524 26660
(.branch 2523 30933
.empty
.empty)
(.branch 2525 31755
.empty
.empty))))
(.branch 2535 31779
(.branch 2531 26627
(.branch 2529 30931
(.branch 2528 25884
(.branch 2527 25845
.empty
.empty)
.empty)
(.branch 2530 31724
.empty
.empty))
(.branch 2533 25843
(.branch 2532 30908
.empty
.empty)
(.branch 2534 26636
.empty
.empty)))
(.branch 2540 86400
(.branch 2538 94022
(.branch 2537 92654
(.branch 2536 92750
.empty
.empty)
.empty)
(.branch 2539 93734
.empty
.empty))
(.branch 2542 87672
(.branch 2541 86688
.empty
.empty)
(.branch 2543 87768
.empty
.empty)))))
(.branch 2562 86737
(.branch 2553 93974
(.branch 2549 92655
(.branch 2547 87769
(.branch 2546 87673
(.branch 2545 86689
.empty
.empty)
.empty)
(.branch 2548 92751
.empty
.empty))
(.branch 2551 93735
(.branch 2550 94023
.empty
.empty)
(.branch 2552 93686
.empty
.empty)))
(.branch 2558 86736
(.branch 2556 87720
(.branch 2555 92798
(.branch 2554 92702
.empty
.empty)
.empty)
(.branch 2557 87624
.empty
.empty))
(.branch 2560 87721
(.branch 2559 86448
.empty
.empty)
(.branch 2561 87625
.empty
.empty))))
(.branch 2571 87734
(.branch 2567 92799
(.branch 2565 93975
(.branch 2564 93687
(.branch 2563 86449
.empty
.empty)
.empty)
(.branch 2566 92703
.empty
.empty))
(.branch 2569 86750
(.branch 2568 86462
.empty
.empty)
(.branch 2570 87638
.empty
.empty)))
(.branch 2575 93672
(.branch 2573 92688
(.branch 2572 92784
.empty
.empty)
(.branch 2574 93960
.empty
.empty))
(.branch 2577 92689
(.branch 2576 92785
.empty
.empty)
(.branch 2578 93961
.empty
.empty))))))))
(.branch 2722 94081
(.branch 2651 86414
(.branch 2615 93735
(.branch 2597 87687
(.branch 2588 93720
(.branch 2584 87782
(.branch 2582 87639
(.branch 2581 86751
(.branch 2580 86463
.empty
.empty)
.empty)
(.branch 2583 87735
.empty
.empty))
(.branch 2586 86702
(.branch 2585 87686
.empty
.empty)
(.branch 2587 86414
.empty
.empty)))
(.branch 2593 94009
(.branch 2591 92736
(.branch 2590 92640
(.branch 2589 94008
.empty
.empty)
.empty)
(.branch 2592 93721
.empty
.empty))
(.branch 2595 92737
(.branch 2594 92641
.empty
.empty)
(.branch 2596 87783
.empty
.empty))))
(.branch 2606 87672
(.branch 2602 94022
(.branch 2600 92750
(.branch 2599 86415
(.branch 2598 86703
.empty
.empty)
.empty)
(.branch 2601 92654
.empty
.empty))
(.branch 2604 86400
(.branch 2603 93734
.empty
.empty)
(.branch 2605 86688
.empty
.empty)))
(.branch 2611 87769
(.branch 2609 86689
(.branch 2608 86401
(.branch 2607 87768
.empty
.empty)
.empty)
(.branch 2610 87673
.empty
.empty))
(.branch 2613 92655
(.branch 2612 92751
.empty
.empty)
(.branch 2614 94023
.empty
.empty)))))
(.branch 2633 86750
(.branch 2624 87721
(.branch 2620 87720
(.branch 2618 92702
(.branch 2617 93974
(.branch 2616 93686
.empty
.empty)
.empty)
(.branch 2619 92798
.empty
.empty))
(.branch 2622 86736
(.branch 2621 87624
.empty
.empty)
(.branch 2623 86448
.empty
.empty)))
(.branch 2629 93975
(.branch 2627 86449
(.branch 2626 86737
(.branch 2625 87625
.empty
.empty)
.empty)
(.branch 2628 93687
.empty
.empty))
(.branch 2631 92799
(.branch 2630 92703
.empty
.empty)
(.branch 2632 86462
.empty
.empty))))
(.branch 2642 93961
(.branch 2638 93960
(.branch 2636 92784
(.branch 2635 87734
(.branch 2634 87638
.empty
.empty)
.empty)
(.branch 2637 92688
.empty
.empty))
(.branch 2640 92785
(.branch 2639 93672
.empty
.empty)
(.branch 2641 92689
.empty
.empty)))
(.branch 2647 87735
(.branch 2645 86751
(.branch 2644 86463
(.branch 2643 93673
.empty
.empty)
.empty)
(.branch 2646 87639
.empty
.empty))
(.branch 2649 87686
(.branch 2648 87782
.empty
.empty)
(.branch 2650 86702
.empty
.empty))))))
(.branch 2687 94416
(.branch 2669 88128
(.branch 2660 87783
(.branch 2656 93721
(.branch 2654 92640
(.branch 2653 94008
(.branch 2652 93720
.empty
.empty)
.empty)
(.branch 2655 92736
.empty
.empty))
(.branch 2658 92641
(.branch 2657 94009
.empty
.empty)
(.branch 2659 92737
.empty
.empty)))
(.branch 2665 88143
(.branch 2663 86415
(.branch 2662 86703
(.branch 2661 87687
.empty
.empty)
.empty)
(.branch 2664 92294
.empty
.empty))
(.branch 2667 94382
(.branch 2666 86055
.empty
.empty)
(.branch 2668 92281
.empty
.empty))))
(.branch 2678 86054
(.branch 2674 86041
(.branch 2672 92280
(.branch 2671 94369
(.branch 2670 86040
.empty
.empty)
.empty)
(.branch 2673 88129
.empty
.empty))
(.branch 2676 92295
(.branch 2675 94368
.empty
.empty)
(.branch 2677 88142
.empty
.empty)))
(.branch 2683 94431
(.branch 2681 88190
(.branch 2680 92247
(.branch 2679 94383
.empty
.empty)
.empty)
(.branch 2682 86006
.empty
.empty))
(.branch 2685 88177
(.branch 2684 92232
.empty
.empty)
(.branch 2686 85993
.empty
.empty)))))
(.branch 2705 92328
(.branch 2696 88095
(.branch 2692 92246
(.branch 2690 85992
(.branch 2689 88176
(.branch 2688 92233
.empty
.empty)
.empty)
(.branch 2691 94417
.empty
.empty))
(.branch 2694 86007
(.branch 2693 88191
.empty
.empty)
(.branch 2695 94430
.empty
.empty)))
(.branch 2701 92329
(.branch 2699 86295
(.branch 2698 94142
(.branch 2697 92342
.empty
.empty)
.empty)
(.branch 2700 88080
.empty
.empty))
(.branch 2703 86280
(.branch 2702 94129
.empty
.empty)
(.branch 2704 88081
.empty
.empty))))
(.branch 2714 94095
(.branch 2710 94143
(.branch 2708 88094
(.branch 2707 86281
(.branch 2706 94128
.empty
.empty)
.empty)
(.branch 2709 92343
.empty
.empty))
(.branch 2712 88046
(.branch 2711 86294
.empty
.empty)
(.branch 2713 92391
.empty
.empty)))
(.branch 2718 94080
(.branch 2716 88033
(.branch 2715 86342
.empty
.empty)
(.branch 2717 92376
.empty
.empty))
(.branch 2720 88032
(.branch 2719 86329
.empty
.empty)
(.branch 2721 92377
.empty
.empty)))))))
(.branch 2794 59895
(.branch 2758 86007
(.branch 2740 92295
(.branch 2731 94382
(.branch 2727 86343
(.branch 2725 92390
(.branch 2724 88047
(.branch 2723 86328
.empty
.empty)
.empty)
(.branch 2726 94094
.empty
.empty))
(.branch 2729 88143
(.branch 2728 92294
.empty
.empty)
(.branch 2730 86055
.empty
.empty)))
(.branch 2736 92280
(.branch 2734 86040
(.branch 2733 88128
(.branch 2732 92281
.empty
.empty)
.empty)
(.branch 2735 94369
.empty
.empty))
(.branch 2738 86041
(.branch 2737 88129
.empty
.empty)
(.branch 2739 94368
.empty
.empty))))
(.branch 2749 88177
(.branch 2745 88190
(.branch 2743 94383
(.branch 2742 86054
(.branch 2741 88142
.empty
.empty)
.empty)
(.branch 2744 92247
.empty
.empty))
(.branch 2747 94431
(.branch 2746 86006
.empty
.empty)
(.branch 2748 92232
.empty
.empty)))
(.branch 2754 85992
(.branch 2752 92233
(.branch 2751 94416
(.branch 2750 85993
.empty
.empty)
.empty)
(.branch 2753 88176
.empty
.empty))
(.branch 2756 92246
(.branch 2755 94417
.empty
.empty)
(.branch 2757 88191
.empty
.empty)))))
(.branch 2776 88046
(.branch 2767 86280
(.branch 2763 86295
(.branch 2761 92342
(.branch 2760 88095
(.branch 2759 94430
.empty
.empty)
.empty)
(.branch 2762 94142
.empty
.empty))
(.branch 2765 92329
(.branch 2764 88080
.empty
.empty)
(.branch 2766 94129
.empty
.empty)))
(.branch 2772 88094
(.branch 2770 94128
(.branch 2769 92328
(.branch 2768 88081
.empty
.empty)
.empty)
(.branch 2771 86281
.empty
.empty))
(.branch 2774 94143
(.branch 2773 92343
.empty
.empty)
(.branch 2775 86294
.empty
.empty))))
(.branch 2785 92377
(.branch 2781 92376
(.branch 2779 86342
(.branch 2778 94095
(.branch 2777 92391
.empty
.empty)
.empty)
(.branch 2780 88033
.empty
.empty))
(.branch 2783 86329
(.branch 2782 94080
.empty
.empty)
(.branch 2784 88032
.empty
.empty)))
(.branch 2790 94094
(.branch 2788 88047
(.branch 2787 86328
(.branch 2786 94081
.empty
.empty)
.empty)
(.branch 2789 92390
.empty
.empty))
(.branch 2792 52958
(.branch 2791 86343
.empty
.empty)
(.branch 2793 59007
.empty
.empty))))))
(.branch 2830 59929
(.branch 2812 60216
(.branch 2803 53832
(.branch 2799 53833
(.branch 2797 58992
(.branch 2796 52945
(.branch 2795 53846
.empty
.empty)
.empty)
(.branch 2798 59880
.empty
.empty))
(.branch 2801 58993
(.branch 2800 52944
.empty
.empty)
(.branch 2802 59881
.empty
.empty)))
(.branch 2808 60231
(.branch 2806 59894
(.branch 2805 59006
(.branch 2804 52959
.empty
.empty)
.empty)
(.branch 2807 53847
.empty
.empty))
(.branch 2810 52622
(.branch 2809 53990
.empty
.empty)
(.branch 2811 58863
.empty
.empty))))
(.branch 2821 53991
(.branch 2817 53976
(.branch 2815 58848
(.branch 2814 52609
(.branch 2813 53977
.empty
.empty)
.empty)
(.branch 2816 60217
.empty
.empty))
(.branch 2819 58849
(.branch 2818 52608
.empty
.empty)
(.branch 2820 60230
.empty
.empty)))
(.branch 2826 59942
(.branch 2824 52911
(.branch 2823 58862
(.branch 2822 52623
.empty
.empty)
.empty)
(.branch 2825 58958
.empty
.empty))
(.branch 2828 52896
(.branch 2827 53895
.empty
.empty)
(.branch 2829 58945
.empty
.empty)))))
(.branch 2848 60168
(.branch 2839 53894
(.branch 2835 53881
(.branch 2833 58944
(.branch 2832 52897
(.branch 2831 53880
.empty
.empty)
.empty)
(.branch 2834 59928
.empty
.empty))
(.branch 2837 58959
(.branch 2836 52910
.empty
.empty)
(.branch 2838 59943
.empty
.empty)))
(.branch 2844 60169
(.branch 2842 52671
(.branch 2841 53943
(.branch 2840 60182
.empty
.empty)
.empty)
(.branch 2843 58910
.empty
.empty))
(.branch 2846 52656
(.branch 2845 53928
.empty
.empty)
(.branch 2847 58897
.empty
.empty))))
(.branch 2857 59007
(.branch 2853 53942
(.branch 2851 58896
(.branch 2850 52657
(.branch 2849 53929
.empty
.empty)
.empty)
(.branch 2852 60183
.empty
.empty))
(.branch 2855 58911
(.branch 2854 52670
.empty
.empty)
(.branch 2856 52958
.empty
.empty)))
(.branch 2861 58992
(.branch 2859 53846
(.branch 2858 59895
.empty
.empty)
(.branch 2860 52945
.empty
.empty))
(.branch 2863 53833
(.branch 2862 59880
.empty
.empty)
(.branch 2864 52944
.empty
.empty)))))))))
(.branch 3152 146
(.branch 3009 53857
(.branch 2937 53870
(.branch 2901 58959
(.branch 2883 58849
(.branch 2874 52622
(.branch 2870 59894
(.branch 2868 52959
(.branch 2867 53832
(.branch 2866 59881
.empty
.empty)
.empty)
(.branch 2869 59006
.empty
.empty))
(.branch 2872 60231
(.branch 2871 53847
.empty
.empty)
(.branch 2873 53990
.empty
.empty)))
(.branch 2879 58848
(.branch 2877 53977
(.branch 2876 60216
(.branch 2875 58863
.empty
.empty)
.empty)
(.branch 2878 52609
.empty
.empty))
(.branch 2881 53976
(.branch 2880 60217
.empty
.empty)
(.branch 2882 52608
.empty
.empty))))
(.branch 2892 52896
(.branch 2888 52911
(.branch 2886 52623
(.branch 2885 53991
(.branch 2884 60230
.empty
.empty)
.empty)
(.branch 2887 58862
.empty
.empty))
(.branch 2890 59942
(.branch 2889 58958
.empty
.empty)
(.branch 2891 53895
.empty
.empty)))
(.branch 2897 58944
(.branch 2895 53880
(.branch 2894 59929
(.branch 2893 58945
.empty
.empty)
.empty)
(.branch 2896 52897
.empty
.empty))
(.branch 2899 53881
(.branch 2898 59928
.empty
.empty)
(.branch 2900 52910
.empty
.empty)))))
(.branch 2919 58911
(.branch 2910 52656
(.branch 2906 52671
(.branch 2904 60182
(.branch 2903 53894
(.branch 2902 59943
.empty
.empty)
.empty)
(.branch 2905 53943
.empty
.empty))
(.branch 2908 60169
(.branch 2907 58910
.empty
.empty)
(.branch 2909 53928
.empty
.empty)))
(.branch 2915 58896
(.branch 2913 53929
(.branch 2912 60168
(.branch 2911 58897
.empty
.empty)
.empty)
(.branch 2914 52657
.empty
.empty))
(.branch 2917 53942
(.branch 2916 60183
.empty
.empty)
(.branch 2918 52670
.empty
.empty))))
(.branch 2928 59953
(.branch 2924 59952
(.branch 2922 52887
(.branch 2921 53919
(.branch 2920 59966
.empty
.empty)
.empty)
(.branch 2923 58934
.empty
.empty))
(.branch 2926 52873
(.branch 2925 53905
.empty
.empty)
(.branch 2927 58920
.empty
.empty)))
(.branch 2933 53918
(.branch 2931 58921
(.branch 2930 52872
(.branch 2929 53904
.empty
.empty)
.empty)
(.branch 2932 59967
.empty
.empty))
(.branch 2935 58935
(.branch 2934 52886
.empty
.empty)
(.branch 2936 59919
.empty
.empty))))))
(.branch 2973 58825
(.branch 2955 53967
(.branch 2946 52921
(.branch 2942 52920
(.branch 2940 59905
(.branch 2939 58983
(.branch 2938 52934
.empty
.empty)
.empty)
(.branch 2941 53856
.empty
.empty))
(.branch 2944 59904
(.branch 2943 58969
.empty
.empty)
(.branch 2945 53857
.empty
.empty)))
(.branch 2951 58982
(.branch 2949 53871
(.branch 2948 59918
(.branch 2947 58968
.empty
.empty)
.empty)
(.branch 2950 52935
.empty
.empty))
(.branch 2953 58886
(.branch 2952 52647
.empty
.empty)
(.branch 2954 60206
.empty
.empty))))
(.branch 2964 52646
(.branch 2960 52632
(.branch 2958 60192
(.branch 2957 58872
(.branch 2956 52633
.empty
.empty)
.empty)
(.branch 2959 53953
.empty
.empty))
(.branch 2962 60193
(.branch 2961 58873
.empty
.empty)
(.branch 2963 53952
.empty
.empty)))
(.branch 2969 58839
(.branch 2967 53966
(.branch 2966 60207
(.branch 2965 58887
.empty
.empty)
.empty)
(.branch 2968 52598
.empty
.empty))
(.branch 2971 54014
(.branch 2970 60255
.empty
.empty)
(.branch 2972 52584
.empty
.empty)))))
(.branch 2991 58920
(.branch 2982 60254
(.branch 2978 60240
(.branch 2976 52585
(.branch 2975 54000
(.branch 2974 60241
.empty
.empty)
.empty)
(.branch 2977 58824
.empty
.empty))
(.branch 2980 52599
(.branch 2979 54001
.empty
.empty)
(.branch 2981 58838
.empty
.empty)))
(.branch 2987 58934
(.branch 2985 53919
(.branch 2984 59966
(.branch 2983 54015
.empty
.empty)
.empty)
(.branch 2986 52887
.empty
.empty))
(.branch 2989 53905
(.branch 2988 59952
.empty
.empty)
(.branch 2990 52873
.empty
.empty))))
(.branch 3000 59919
(.branch 2996 59967
(.branch 2994 52872
(.branch 2993 53904
(.branch 2992 59953
.empty
.empty)
.empty)
(.branch 2995 58921
.empty
.empty))
(.branch 2998 52886
(.branch 2997 53918
.empty
.empty)
(.branch 2999 58935
.empty
.empty)))
(.branch 3005 53856
(.branch 3003 58983
(.branch 3002 52934
(.branch 3001 53870
.empty
.empty)
.empty)
(.branch 3004 59905
.empty
.empty))
(.branch 3007 58969
(.branch 3006 52920
.empty
.empty)
(.branch 3008 59904
.empty
.empty)))))))
(.branch 3081 34538
(.branch 3045 58838
(.branch 3027 53952
(.branch 3018 60206
(.branch 3014 52935
(.branch 3012 59918
(.branch 3011 58968
(.branch 3010 52921
.empty
.empty)
.empty)
(.branch 3013 53871
.empty
.empty))
(.branch 3016 52647
(.branch 3015 58982
.empty
.empty)
(.branch 3017 58886
.empty
.empty)))
(.branch 3023 53953
(.branch 3021 58872
(.branch 3020 52633
(.branch 3019 53967
.empty
.empty)
.empty)
(.branch 3022 60192
.empty
.empty))
(.branch 3025 58873
(.branch 3024 52632
.empty
.empty)
(.branch 3026 60193
.empty
.empty))))
(.branch 3036 52584
(.branch 3032 52598
(.branch 3030 60207
(.branch 3029 58887
(.branch 3028 52646
.empty
.empty)
.empty)
(.branch 3031 53966
.empty
.empty))
(.branch 3034 60255
(.branch 3033 58839
.empty
.empty)
(.branch 3035 54014
.empty
.empty)))
(.branch 3041 58824
(.branch 3039 54000
(.branch 3038 60241
(.branch 3037 58825
.empty
.empty)
.empty)
(.branch 3040 52585
.empty
.empty))
(.branch 3043 54001
(.branch 3042 60240
.empty
.empty)
(.branch 3044 52599
.empty
.empty)))))
(.branch 3063 162
(.branch 3054 34561
(.branch 3050 5
(.branch 3048 130
(.branch 3047 54015
(.branch 3046 60254
.empty
.empty)
.empty)
(.branch 3049 27
.empty
.empty))
(.branch 3052 34572
(.branch 3051 407
.empty
.empty)
(.branch 3053 34562
.empty
.empty)))
(.branch 3059 34587
(.branch 3057 34586
(.branch 3056 34548
(.branch 3055 34563
.empty
.empty)
.empty)
(.branch 3058 34585
.empty
.empty))
(.branch 3061 305
(.branch 3060 437
.empty
.empty)
(.branch 3062 283
.empty
.empty))))
(.branch 3072 451
(.branch 3068 422
(.branch 3066 34577
(.branch 3065 34578
(.branch 3064 34556
.empty
.empty)
.empty)
(.branch 3067 34579
.empty
.empty))
(.branch 3070 282
(.branch 3069 304
.empty
.empty)
(.branch 3071 147
.empty
.empty)))
(.branch 3077 34598
(.branch 3075 176
(.branch 3074 284
(.branch 3073 306
.empty
.empty)
.empty)
(.branch 3076 34536
.empty
.empty))
(.branch 3079 34599
(.branch 3078 34597
.empty
.empty)
(.branch 3080 34596
.empty
.empty))))))
(.branch 3117 34562
(.branch 3099 438
(.branch 3090 6
(.branch 3086 8
(.branch 3084 175
(.branch 3083 34539
(.branch 3082 34537
.empty
.empty)
.empty)
(.branch 3085 30
.empty
.empty))
(.branch 3088 146
(.branch 3087 452
.empty
.empty)
(.branch 3089 28
.empty
.empty)))
(.branch 3095 34559
(.branch 3093 34558
(.branch 3092 34576
(.branch 3091 423
.empty
.empty)
.empty)
(.branch 3094 34557
.empty
.empty))
(.branch 3097 29
(.branch 3096 161
.empty
.empty)
(.branch 3098 7
.empty
.empty))))
(.branch 3108 406
(.branch 3104 34560
(.branch 3102 34549
(.branch 3101 34550
(.branch 3100 34584
.empty
.empty)
.empty)
(.branch 3103 34551
.empty
.empty))
(.branch 3106 34573
(.branch 3105 34574
.empty
.empty)
(.branch 3107 34575
.empty
.empty)))
(.branch 3113 27
(.branch 3111 131
(.branch 3110 281
(.branch 3109 303
.empty
.empty)
.empty)
(.branch 3112 130
.empty
.empty))
(.branch 3115 407
(.branch 3114 5
.empty
.empty)
(.branch 3116 34572
.empty
.empty)))))
(.branch 3135 147
(.branch 3126 283
(.branch 3122 34585
(.branch 3120 34548
(.branch 3119 34563
(.branch 3118 34561
.empty
.empty)
.empty)
(.branch 3121 34586
.empty
.empty))
(.branch 3124 437
(.branch 3123 34587
.empty
.empty)
(.branch 3125 305
.empty
.empty)))
(.branch 3131 34579
(.branch 3129 34578
(.branch 3128 34556
(.branch 3127 162
.empty
.empty)
.empty)
(.branch 3130 34577
.empty
.empty))
(.branch 3133 304
(.branch 3132 422
.empty
.empty)
(.branch 3134 282
.empty
.empty))))
(.branch 3144 34596
(.branch 3140 34536
(.branch 3138 284
(.branch 3137 306
(.branch 3136 451
.empty
.empty)
.empty)
(.branch 3139 176
.empty
.empty))
(.branch 3142 34597
(.branch 3141 34598
.empty
.empty)
(.branch 3143 34599
.empty
.empty)))
(.branch 3148 175
(.branch 3146 34537
(.branch 3145 34538
.empty
.empty)
(.branch 3147 34539
.empty
.empty))
(.branch 3150 8
(.branch 3149 30
.empty
.empty)
(.branch 3151 452
.empty
.empty))))))))
(.branch 3295 34662
(.branch 3224 598
(.branch 3188 10152
(.branch 3170 34573
(.branch 3161 29
(.branch 3157 34558
(.branch 3155 423
(.branch 3154 6
(.branch 3153 28
.empty
.empty)
.empty)
(.branch 3156 34576
.empty
.empty))
(.branch 3159 34559
(.branch 3158 34557
.empty
.empty)
(.branch 3160 161
.empty
.empty)))
(.branch 3166 34549
(.branch 3164 34584
(.branch 3163 438
(.branch 3162 7
.empty
.empty)
.empty)
(.branch 3165 34550
.empty
.empty))
(.branch 3168 34560
(.branch 3167 34551
.empty
.empty)
(.branch 3169 34574
.empty
.empty))))
(.branch 3179 10167
(.branch 3175 131
(.branch 3173 303
(.branch 3172 406
(.branch 3171 34575
.empty
.empty)
.empty)
(.branch 3174 281
.empty
.empty))
(.branch 3177 10367
(.branch 3176 10215
.empty
.empty)
(.branch 3178 10371
.empty
.empty)))
(.branch 3184 32969
(.branch 3182 33210
(.branch 3181 33226
(.branch 3180 32970
.empty
.empty)
.empty)
(.branch 3183 32965
.empty
.empty))
(.branch 3186 33209
(.branch 3185 33225
.empty
.empty)
(.branch 3187 32966
.empty
.empty)))))
(.branch 3206 10364
(.branch 3197 33221
(.branch 3193 10383
(.branch 3191 10200
(.branch 3190 10380
(.branch 3189 10384
.empty
.empty)
.empty)
(.branch 3192 10203
.empty
.empty))
(.branch 3195 10155
(.branch 3194 10387
.empty
.empty)
(.branch 3196 32954
.empty
.empty)))
(.branch 3202 33238
(.branch 3200 32953
(.branch 3199 32981
(.branch 3198 33237
.empty
.empty)
.empty)
(.branch 3201 33222
.empty
.empty))
(.branch 3204 10164
(.branch 3203 32982
.empty
.empty)
(.branch 3205 10368
.empty
.empty))))
(.branch 3215 34650
(.branch 3211 585
(.branch 3209 1109
(.branch 3208 597
(.branch 3207 10212
.empty
.empty)
.empty)
(.branch 3210 1110
.empty
.empty))
(.branch 3213 34706
(.branch 3212 34602
.empty
.empty)
(.branch 3214 34702
.empty
.empty)))
(.branch 3220 570
(.branch 3218 34701
(.branch 3217 34705
(.branch 3216 34601
.empty
.empty)
.empty)
(.branch 3219 34649
.empty
.empty))
(.branch 3222 1081
(.branch 3221 1082
.empty
.empty)
(.branch 3223 582
.empty
.empty))))))
(.branch 3260 32954
(.branch 3242 10371
(.branch 3233 34689
(.branch 3229 34690
(.branch 3227 586
(.branch 3226 1098
(.branch 3225 1097
.empty
.empty)
.empty)
(.branch 3228 34614
.empty
.empty))
(.branch 3231 34662
(.branch 3230 34686
.empty
.empty)
(.branch 3232 34613
.empty
.empty)))
(.branch 3238 1093
(.branch 3236 569
(.branch 3235 34661
(.branch 3234 34685
.empty
.empty)
.empty)
(.branch 3237 1094
.empty
.empty))
(.branch 3240 10215
(.branch 3239 581
.empty
.empty)
(.branch 3241 10367
.empty
.empty))))
(.branch 3251 32966
(.branch 3247 32965
(.branch 3245 33226
(.branch 3244 32970
(.branch 3243 10167
.empty
.empty)
.empty)
(.branch 3246 33210
.empty
.empty))
(.branch 3249 33225
(.branch 3248 32969
.empty
.empty)
(.branch 3250 33209
.empty
.empty)))
(.branch 3256 10203
(.branch 3254 10380
(.branch 3253 10384
(.branch 3252 10152
.empty
.empty)
.empty)
(.branch 3255 10200
.empty
.empty))
(.branch 3258 10387
(.branch 3257 10383
.empty
.empty)
(.branch 3259 10155
.empty
.empty)))))
(.branch 3278 34702
(.branch 3269 10368
(.branch 3265 33222
(.branch 3263 32981
(.branch 3262 33237
(.branch 3261 33221
.empty
.empty)
.empty)
(.branch 3264 32953
.empty
.empty))
(.branch 3267 32982
(.branch 3266 33238
.empty
.empty)
(.branch 3268 10164
.empty
.empty)))
(.branch 3274 1110
(.branch 3272 597
(.branch 3271 10212
(.branch 3270 10364
.empty
.empty)
.empty)
(.branch 3273 1109
.empty
.empty))
(.branch 3276 34602
(.branch 3275 585
.empty
.empty)
(.branch 3277 34706
.empty
.empty))))
(.branch 3287 582
(.branch 3283 34649
(.branch 3281 34705
(.branch 3280 34601
(.branch 3279 34650
.empty
.empty)
.empty)
(.branch 3282 34701
.empty
.empty))
(.branch 3285 1082
(.branch 3284 570
.empty
.empty)
(.branch 3286 1081
.empty
.empty)))
(.branch 3291 586
(.branch 3289 1097
(.branch 3288 598
.empty
.empty)
(.branch 3290 1098
.empty
.empty))
(.branch 3293 34690
(.branch 3292 34614
.empty
.empty)
(.branch 3294 34686
.empty
.empty)))))))
(.branch 3367 31663
(.branch 3331 48897
(.branch 3313 48697
(.branch 3304 25651
(.branch 3300 569
(.branch 3298 34685
(.branch 3297 34689
(.branch 3296 34613
.empty
.empty)
.empty)
(.branch 3299 34661
.empty
.empty))
(.branch 3302 1093
(.branch 3301 1094
.empty
.empty)
(.branch 3303 581
.empty
.empty)))
(.branch 3309 48698
(.branch 3307 25692
(.branch 3306 30763
(.branch 3305 30820
.empty
.empty)
.empty)
(.branch 3308 47669
.empty
.empty))
(.branch 3311 47706
(.branch 3310 48725
.empty
.empty)
(.branch 3312 47670
.empty
.empty))))
(.branch 3322 26673
(.branch 3318 30811
(.branch 3316 25699
(.branch 3315 47705
(.branch 3314 48726
.empty
.empty)
.empty)
(.branch 3317 30772
.empty
.empty))
(.branch 3320 31657
(.branch 3319 25644
.empty
.empty)
(.branch 3321 26718
.empty
.empty)))
(.branch 3327 48898
(.branch 3325 47906
(.branch 3324 48909
(.branch 3323 31718
.empty
.empty)
.empty)
(.branch 3326 47853
.empty
.empty))
(.branch 3329 47905
(.branch 3328 48910
.empty
.empty)
(.branch 3330 47854
.empty
.empty)))))
(.branch 3349 30765
(.branch 3340 47697
(.branch 3336 25642
(.branch 3334 26721
(.branch 3333 26670
(.branch 3332 31705
.empty
.empty)
.empty)
(.branch 3335 31670
.empty
.empty))
(.branch 3338 30770
(.branch 3337 30813
.empty
.empty)
(.branch 3339 25701
.empty
.empty)))
(.branch 3345 48733
(.branch 3343 47678
(.branch 3342 48689
(.branch 3341 48734
.empty
.empty)
.empty)
(.branch 3344 47698
.empty
.empty))
(.branch 3347 47677
(.branch 3346 48690
.empty
.empty)
(.branch 3348 25690
.empty
.empty))))
(.branch 3358 47881
(.branch 3354 26664
(.branch 3352 31664
(.branch 3351 25653
(.branch 3350 30818
.empty
.empty)
.empty)
(.branch 3353 26727
.empty
.empty))
(.branch 3356 48873
(.branch 3355 31711
.empty
.empty)
(.branch 3357 47878
.empty
.empty)))
(.branch 3363 48933
(.branch 3361 47877
(.branch 3360 48874
(.branch 3359 48934
.empty
.empty)
.empty)
(.branch 3362 47882
.empty
.empty))
(.branch 3365 26679
(.branch 3364 31712
.empty
.empty)
(.branch 3366 26712
.empty
.empty))))))
(.branch 3403 25701
(.branch 3385 26718
(.branch 3376 47670
(.branch 3372 47669
(.branch 3370 30763
(.branch 3369 30820
(.branch 3368 25651
.empty
.empty)
.empty)
(.branch 3371 25692
.empty
.empty))
(.branch 3374 48725
(.branch 3373 48698
.empty
.empty)
(.branch 3375 47706
.empty
.empty)))
(.branch 3381 30772
(.branch 3379 47705
(.branch 3378 48726
(.branch 3377 48697
.empty
.empty)
.empty)
(.branch 3380 25699
.empty
.empty))
(.branch 3383 25644
(.branch 3382 30811
.empty
.empty)
(.branch 3384 31657
.empty
.empty))))
(.branch 3394 47854
(.branch 3390 47853
(.branch 3388 48909
(.branch 3387 31718
(.branch 3386 26673
.empty
.empty)
.empty)
(.branch 3389 47906
.empty
.empty))
(.branch 3392 48910
(.branch 3391 48898
.empty
.empty)
(.branch 3393 47905
.empty
.empty)))
(.branch 3399 31670
(.branch 3397 26670
(.branch 3396 31705
(.branch 3395 48897
.empty
.empty)
.empty)
(.branch 3398 26721
.empty
.empty))
(.branch 3401 30813
(.branch 3400 25642
.empty
.empty)
(.branch 3402 30770
.empty
.empty)))))
(.branch 3421 47878
(.branch 3412 25690
(.branch 3408 47698
(.branch 3406 48689
(.branch 3405 48734
(.branch 3404 47697
.empty
.empty)
.empty)
(.branch 3407 47678
.empty
.empty))
(.branch 3410 48690
(.branch 3409 48733
.empty
.empty)
(.branch 3411 47677
.empty
.empty)))
(.branch 3417 26727
(.branch 3415 25653
(.branch 3414 30818
(.branch 3413 30765
.empty
.empty)
.empty)
(.branch 3416 31664
.empty
.empty))
(.branch 3419 31711
(.branch 3418 26664
.empty
.empty)
(.branch 3420 48873
.empty
.empty))))
(.branch 3430 26712
(.branch 3426 47882
(.branch 3424 48874
(.branch 3423 48934
(.branch 3422 47881
.empty
.empty)
.empty)
(.branch 3425 47877
.empty
.empty))
(.branch 3428 31712
(.branch 3427 48933
.empty
.empty)
(.branch 3429 26679
.empty
.empty)))
(.branch 3434 48630
(.branch 3432 25259
(.branch 3431 31663
.empty
.empty)
(.branch 3433 48629
.empty
.empty))
(.branch 3436 30570
(.branch 3435 25307
.empty
.empty)
(.branch 3437 47601
.empty
.empty))))))))))
(.branch 4011 25319
(.branch 3725 34669
(.branch 3582 287
(.branch 3510 48658
(.branch 3474 47974
(.branch 3456 32049
(.branch 3447 25314
(.branch 3443 30627
(.branch 3441 47637
(.branch 3440 30579
(.branch 3439 30618
.empty
.empty)
.empty)
(.branch 3442 47638
.empty
.empty))
(.branch 3445 48657
(.branch 3444 25266
.empty
.empty)
(.branch 3446 48658
.empty
.empty)))
(.branch 3452 32040
(.branch 3450 48942
(.branch 3449 48941
(.branch 3448 26985
.empty
.empty)
.empty)
(.branch 3451 27033
.empty
.empty))
(.branch 3454 47914
(.branch 3453 47913
.empty
.empty)
(.branch 3455 32088
.empty
.empty))))
(.branch 3465 48965
(.branch 3461 48969
(.branch 3459 32097
(.branch 3458 47950
(.branch 3457 47949
.empty
.empty)
.empty)
(.branch 3460 26992
.empty
.empty))
(.branch 3463 27040
(.branch 3462 48970
.empty
.empty)
(.branch 3464 26991
.empty
.empty)))
(.branch 3470 47938
(.branch 3468 32046
(.branch 3467 27039
(.branch 3466 48966
.empty
.empty)
.empty)
(.branch 3469 47937
.empty
.empty))
(.branch 3472 32055
(.branch 3471 32094
.empty
.empty)
(.branch 3473 47973
.empty
.empty)))))
(.branch 3492 25268
(.branch 3483 25309
(.branch 3479 27046
(.branch 3477 48993
(.branch 3476 26998
(.branch 3475 32103
.empty
.empty)
.empty)
(.branch 3478 48994
.empty
.empty))
(.branch 3481 48637
(.branch 3480 25261
.empty
.empty)
(.branch 3482 48638
.empty
.empty)))
(.branch 3488 30581
(.branch 3486 47610
(.branch 3485 47609
(.branch 3484 30572
.empty
.empty)
.empty)
(.branch 3487 30620
.empty
.empty))
(.branch 3490 47646
(.branch 3489 47645
.empty
.empty)
(.branch 3491 30629
.empty
.empty))))
(.branch 3501 47601
(.branch 3497 48629
(.branch 3495 25316
(.branch 3494 48666
(.branch 3493 48665
.empty
.empty)
.empty)
(.branch 3496 25259
.empty
.empty))
(.branch 3499 25307
(.branch 3498 48630
.empty
.empty)
(.branch 3500 30570
.empty
.empty)))
(.branch 3506 47638
(.branch 3504 30579
(.branch 3503 30618
(.branch 3502 47602
.empty
.empty)
.empty)
(.branch 3505 47637
.empty
.empty))
(.branch 3508 25266
(.branch 3507 30627
.empty
.empty)
(.branch 3509 48657
.empty
.empty))))))
(.branch 3546 48638
(.branch 3528 26991
(.branch 3519 32088
(.branch 3515 27033
(.branch 3513 48941
(.branch 3512 26985
(.branch 3511 25314
.empty
.empty)
.empty)
(.branch 3514 48942
.empty
.empty))
(.branch 3517 47913
(.branch 3516 32040
.empty
.empty)
(.branch 3518 47914
.empty
.empty)))
(.branch 3524 26992
(.branch 3522 47950
(.branch 3521 47949
(.branch 3520 32049
.empty
.empty)
.empty)
(.branch 3523 32097
.empty
.empty))
(.branch 3526 48970
(.branch 3525 48969
.empty
.empty)
(.branch 3527 27040
.empty
.empty))))
(.branch 3537 47973
(.branch 3533 47937
(.branch 3531 27039
(.branch 3530 48966
(.branch 3529 48965
.empty
.empty)
.empty)
(.branch 3532 32046
.empty
.empty))
(.branch 3535 32094
(.branch 3534 47938
.empty
.empty)
(.branch 3536 32055
.empty
.empty)))
(.branch 3542 48994
(.branch 3540 26998
(.branch 3539 32103
(.branch 3538 47974
.empty
.empty)
.empty)
(.branch 3541 48993
.empty
.empty))
(.branch 3544 25261
(.branch 3543 27046
.empty
.empty)
(.branch 3545 48637
.empty
.empty)))))
(.branch 3564 33036
(.branch 3555 30629
(.branch 3551 30620
(.branch 3549 47609
(.branch 3548 30572
(.branch 3547 25309
.empty
.empty)
.empty)
(.branch 3550 47610
.empty
.empty))
(.branch 3553 47645
(.branch 3552 30581
.empty
.empty)
(.branch 3554 47646
.empty
.empty)))
(.branch 3560 56
(.branch 3558 48666
(.branch 3557 48665
(.branch 3556 25268
.empty
.empty)
.empty)
(.branch 3559 25316
.empty
.empty))
(.branch 3562 1
(.branch 3561 23
.empty
.empty)
(.branch 3563 333
.empty
.empty))))
(.branch 3573 34
(.branch 3569 33002
(.branch 3567 33027
(.branch 3566 33025
(.branch 3565 33026
.empty
.empty)
.empty)
(.branch 3568 33060
.empty
.empty))
(.branch 3571 33003
(.branch 3570 33001
.empty
.empty)
(.branch 3572 221
.empty
.empty)))
(.branch 3578 33049
(.branch 3576 33012
(.branch 3575 498
(.branch 3574 12
.empty
.empty)
.empty)
(.branch 3577 33050
.empty
.empty))
(.branch 3580 487
(.branch 3579 33051
.empty
.empty)
(.branch 3581 309
.empty
.empty)))))))
(.branch 3654 33021
(.branch 3618 33037
(.branch 3600 211
(.branch 3591 33023
(.branch 3587 353
(.branch 3585 24
(.branch 3584 76
(.branch 3583 212
.empty
.empty)
.empty)
(.branch 3586 2
.empty
.empty))
(.branch 3589 33022
(.branch 3588 33040
.empty
.empty)
(.branch 3590 33021
.empty
.empty)))
(.branch 3596 352
(.branch 3594 33041
(.branch 3593 33042
(.branch 3592 33020
.empty
.empty)
.empty)
(.branch 3595 33043
.empty
.empty))
(.branch 3598 278
(.branch 3597 300
.empty
.empty)
(.branch 3599 77
.empty
.empty))))
(.branch 3609 310
(.branch 3605 33014
(.branch 3603 488
(.branch 3602 11
(.branch 3601 33
.empty
.empty)
.empty)
(.branch 3604 33048
.empty
.empty))
(.branch 3607 33015
(.branch 3606 33013
.empty
.empty)
(.branch 3608 497
.empty
.empty)))
(.branch 3614 33061
(.branch 3612 33000
(.branch 3611 222
(.branch 3610 288
.empty
.empty)
.empty)
(.branch 3613 33062
.empty
.empty))
(.branch 3616 33024
(.branch 3615 33063
.empty
.empty)
(.branch 3617 33038
.empty
.empty)))))
(.branch 3636 221
(.branch 3627 333
(.branch 3623 57
(.branch 3621 299
(.branch 3620 332
(.branch 3619 33039
.empty
.empty)
.empty)
(.branch 3622 277
.empty
.empty))
(.branch 3625 23
(.branch 3624 56
.empty
.empty)
(.branch 3626 1
.empty
.empty)))
(.branch 3632 33060
(.branch 3630 33025
(.branch 3629 33026
(.branch 3628 33036
.empty
.empty)
.empty)
(.branch 3631 33027
.empty
.empty))
(.branch 3634 33001
(.branch 3633 33002
.empty
.empty)
(.branch 3635 33003
.empty
.empty))))
(.branch 3645 309
(.branch 3641 33050
(.branch 3639 498
(.branch 3638 12
(.branch 3637 34
.empty
.empty)
.empty)
(.branch 3640 33012
.empty
.empty))
(.branch 3643 33051
(.branch 3642 33049
.empty
.empty)
(.branch 3644 487
.empty
.empty)))
(.branch 3650 2
(.branch 3648 76
(.branch 3647 212
(.branch 3646 287
.empty
.empty)
.empty)
(.branch 3649 24
.empty
.empty))
(.branch 3652 33040
(.branch 3651 353
.empty
.empty)
(.branch 3653 33022
.empty
.empty))))))
(.branch 3690 1070
(.branch 3672 497
(.branch 3663 77
(.branch 3659 33043
(.branch 3657 33042
(.branch 3656 33020
(.branch 3655 33023
.empty
.empty)
.empty)
(.branch 3658 33041
.empty
.empty))
(.branch 3661 300
(.branch 3660 352
.empty
.empty)
(.branch 3662 278
.empty
.empty)))
(.branch 3668 33048
(.branch 3666 11
(.branch 3665 33
(.branch 3664 211
.empty
.empty)
.empty)
(.branch 3667 488
.empty
.empty))
(.branch 3670 33013
(.branch 3669 33014
.empty
.empty)
(.branch 3671 33015
.empty
.empty))))
(.branch 3681 33038
(.branch 3677 33062
(.branch 3675 222
(.branch 3674 288
(.branch 3673 310
.empty
.empty)
.empty)
(.branch 3676 33000
.empty
.empty))
(.branch 3679 33063
(.branch 3678 33061
.empty
.empty)
(.branch 3680 33024
.empty
.empty)))
(.branch 3686 277
(.branch 3684 332
(.branch 3683 33039
(.branch 3682 33037
.empty
.empty)
.empty)
(.branch 3685 299
.empty
.empty))
(.branch 3688 10205
(.branch 3687 57
.empty
.empty)
(.branch 3689 1069
.empty
.empty)))))
(.branch 3708 34610
(.branch 3699 34606
(.branch 3695 34605
(.branch 3693 33213
(.branch 3692 34653
(.branch 3691 10157
.empty
.empty)
.empty)
(.branch 3694 33229
.empty
.empty))
(.branch 3697 33214
(.branch 3696 34654
.empty
.empty)
(.branch 3698 33230
.empty
.empty)))
(.branch 3704 10206
(.branch 3702 1121
(.branch 3701 1122
(.branch 3700 10162
.empty
.empty)
.empty)
(.branch 3703 10210
.empty
.empty))
(.branch 3706 1118
(.branch 3705 1117
.empty
.empty)
(.branch 3707 10158
.empty
.empty))))
(.branch 3717 1074
(.branch 3713 33218
(.branch 3711 34658
(.branch 3710 33233
(.branch 3709 33217
.empty
.empty)
.empty)
(.branch 3712 34609
.empty
.empty))
(.branch 3715 34657
(.branch 3714 33234
.empty
.empty)
(.branch 3716 10161
.empty
.empty)))
(.branch 3721 10349
(.branch 3719 10209
(.branch 3718 1073
.empty
.empty)
(.branch 3720 564
.empty
.empty))
(.branch 3723 552
(.branch 3722 10353
.empty
.empty)
(.branch 3724 32994
.empty
.empty))))))))
(.branch 3868 47693
(.branch 3797 10402
(.branch 3761 33214
(.branch 3743 32945
(.branch 3734 10398
(.branch 3730 34674
(.branch 3728 32993
(.branch 3727 32941
(.branch 3726 34673
.empty
.empty)
.empty)
(.branch 3729 34670
.empty
.empty))
(.branch 3732 603
(.branch 3731 32942
.empty
.empty)
(.branch 3733 10402
.empty
.empty)))
(.branch 3739 600
(.branch 3737 10350
(.branch 3736 612
(.branch 3735 615
.empty
.empty)
.empty)
(.branch 3738 10354
.empty
.empty))
(.branch 3741 34722
(.branch 3740 32990
.empty
.empty)
(.branch 3742 34718
.empty
.empty))))
(.branch 3752 10205
(.branch 3748 555
(.branch 3746 34717
(.branch 3745 34721
(.branch 3744 32989
.empty
.empty)
.empty)
(.branch 3747 32946
.empty
.empty))
(.branch 3750 10397
(.branch 3749 10401
.empty
.empty)
(.branch 3751 567
.empty
.empty)))
(.branch 3757 33213
(.branch 3755 10157
(.branch 3754 1070
(.branch 3753 1069
.empty
.empty)
.empty)
(.branch 3756 34653
.empty
.empty))
(.branch 3759 34605
(.branch 3758 33229
.empty
.empty)
(.branch 3760 34654
.empty
.empty)))))
(.branch 3779 34657
(.branch 3770 1118
(.branch 3766 1121
(.branch 3764 10162
(.branch 3763 34606
(.branch 3762 33230
.empty
.empty)
.empty)
(.branch 3765 1122
.empty
.empty))
(.branch 3768 10206
(.branch 3767 10210
.empty
.empty)
(.branch 3769 1117
.empty
.empty)))
(.branch 3775 34658
(.branch 3773 33217
(.branch 3772 34610
(.branch 3771 10158
.empty
.empty)
.empty)
(.branch 3774 33233
.empty
.empty))
(.branch 3777 33218
(.branch 3776 34609
.empty
.empty)
(.branch 3778 33234
.empty
.empty))))
(.branch 3788 32994
(.branch 3784 564
(.branch 3782 1073
(.branch 3781 1074
(.branch 3780 10161
.empty
.empty)
.empty)
(.branch 3783 10209
.empty
.empty))
(.branch 3786 10353
(.branch 3785 10349
.empty
.empty)
(.branch 3787 552
.empty
.empty)))
(.branch 3793 34670
(.branch 3791 32941
(.branch 3790 34673
(.branch 3789 34669
.empty
.empty)
.empty)
(.branch 3792 32993
.empty
.empty))
(.branch 3795 32942
(.branch 3794 34674
.empty
.empty)
(.branch 3796 603
.empty
.empty))))))
(.branch 3833 30808
(.branch 3815 567
(.branch 3806 34718
(.branch 3802 10354
(.branch 3800 612
(.branch 3799 615
(.branch 3798 10398
.empty
.empty)
.empty)
(.branch 3801 10350
.empty
.empty))
(.branch 3804 32990
(.branch 3803 600
.empty
.empty)
(.branch 3805 34722
.empty
.empty)))
(.branch 3811 32946
(.branch 3809 34721
(.branch 3808 32989
(.branch 3807 32945
.empty
.empty)
.empty)
(.branch 3810 34717
.empty
.empty))
(.branch 3813 10401
(.branch 3812 555
.empty
.empty)
(.branch 3814 10397
.empty
.empty))))
(.branch 3824 48894
(.branch 3820 48893
(.branch 3818 26669
(.branch 3817 26722
(.branch 3816 25647
.empty
.empty)
.empty)
(.branch 3819 25696
.empty
.empty))
(.branch 3822 48709
(.branch 3821 48714
.empty
.empty)
(.branch 3823 48914
.empty
.empty)))
(.branch 3829 26674
(.branch 3827 48913
(.branch 3826 48710
(.branch 3825 48713
.empty
.empty)
.empty)
(.branch 3828 25695
.empty
.empty))
(.branch 3831 25648
(.branch 3830 26717
.empty
.empty)
(.branch 3832 31669
.empty
.empty)))))
(.branch 3851 25702
(.branch 3842 47902
(.branch 3838 47901
(.branch 3836 47717
(.branch 3835 31706
(.branch 3834 30775
.empty
.empty)
.empty)
(.branch 3837 47858
.empty
.empty))
(.branch 3840 47718
(.branch 3839 47658
.empty
.empty)
(.branch 3841 47857
.empty
.empty)))
(.branch 3847 31658
(.branch 3845 30760
(.branch 3844 31717
(.branch 3843 47657
.empty
.empty)
.empty)
(.branch 3846 30823
.empty
.empty))
(.branch 3849 26724
(.branch 3848 25641
.empty
.empty)
(.branch 3850 26667
.empty
.empty))))
(.branch 3860 25689
(.branch 3856 48886
(.branch 3854 48685
(.branch 3853 48738
(.branch 3852 48885
.empty
.empty)
.empty)
(.branch 3855 48922
.empty
.empty))
(.branch 3858 48686
(.branch 3857 48737
.empty
.empty)
(.branch 3859 48921
.empty
.empty)))
(.branch 3864 31667
(.branch 3862 26715
(.branch 3861 26676
.empty
.empty)
(.branch 3863 25654
.empty
.empty))
(.branch 3866 30769
(.branch 3865 30814
.empty
.empty)
(.branch 3867 31708
.empty
.empty)))))))
(.branch 3940 31715
(.branch 3904 47718
(.branch 3886 48709
(.branch 3877 30766
(.branch 3873 47865
(.branch 3871 47682
(.branch 3870 47893
(.branch 3869 47866
.empty
.empty)
.empty)
(.branch 3872 47694
.empty
.empty))
(.branch 3875 47681
(.branch 3874 47894
.empty
.empty)
(.branch 3876 31715
.empty
.empty)))
(.branch 3882 26669
(.branch 3880 25647
(.branch 3879 31660
(.branch 3878 30817
.empty
.empty)
.empty)
(.branch 3881 26722
.empty
.empty))
(.branch 3884 48893
(.branch 3883 25696
.empty
.empty)
(.branch 3885 48714
.empty
.empty))))
(.branch 3895 25648
(.branch 3891 48913
(.branch 3889 48713
(.branch 3888 48894
(.branch 3887 48914
.empty
.empty)
.empty)
(.branch 3890 48710
.empty
.empty))
(.branch 3893 26674
(.branch 3892 25695
.empty
.empty)
(.branch 3894 26717
.empty
.empty)))
(.branch 3900 47717
(.branch 3898 30775
(.branch 3897 30808
(.branch 3896 31669
.empty
.empty)
.empty)
(.branch 3899 31706
.empty
.empty))
(.branch 3902 47901
(.branch 3901 47858
.empty
.empty)
(.branch 3903 47658
.empty
.empty)))))
(.branch 3922 48686
(.branch 3913 26724
(.branch 3909 30760
(.branch 3907 47657
(.branch 3906 47902
(.branch 3905 47857
.empty
.empty)
.empty)
(.branch 3908 31717
.empty
.empty))
(.branch 3911 31658
(.branch 3910 30823
.empty
.empty)
(.branch 3912 25641
.empty
.empty)))
(.branch 3918 48685
(.branch 3916 48885
(.branch 3915 25702
(.branch 3914 26667
.empty
.empty)
.empty)
(.branch 3917 48738
.empty
.empty))
(.branch 3920 48886
(.branch 3919 48922
.empty
.empty)
(.branch 3921 48737
.empty
.empty))))
(.branch 3931 31708
(.branch 3927 25654
(.branch 3925 26676
(.branch 3924 25689
(.branch 3923 48921
.empty
.empty)
.empty)
(.branch 3926 26715
.empty
.empty))
(.branch 3929 30814
(.branch 3928 31667
.empty
.empty)
(.branch 3930 30769
.empty
.empty)))
(.branch 3936 47694
(.branch 3934 47893
(.branch 3933 47866
(.branch 3932 47693
.empty
.empty)
.empty)
(.branch 3935 47682
.empty
.empty))
(.branch 3938 47894
(.branch 3937 47865
.empty
.empty)
(.branch 3939 47681
.empty
.empty))))))
(.branch 3976 30582
(.branch 3958 48654
(.branch 3949 48989
(.branch 3945 48677
(.branch 3943 31660
(.branch 3942 30817
(.branch 3941 30766
.empty
.empty)
.empty)
(.branch 3944 25271
.empty
.empty))
(.branch 3947 25319
(.branch 3946 48678
.empty
.empty)
(.branch 3948 26997
.empty
.empty)))
(.branch 3954 48982
(.branch 3952 26995
(.branch 3951 27045
(.branch 3950 48990
.empty
.empty)
.empty)
(.branch 3953 48981
.empty
.empty))
(.branch 3956 25265
(.branch 3955 27043
.empty
.empty)
(.branch 3957 48653
.empty
.empty))))
(.branch 3967 32093
(.branch 3963 30623
(.branch 3961 47621
(.branch 3960 30575
(.branch 3959 25313
.empty
.empty)
.empty)
(.branch 3962 47622
.empty
.empty))
(.branch 3965 47933
(.branch 3964 32045
.empty
.empty)
(.branch 3966 47934
.empty
.empty)))
(.branch 3972 30569
(.branch 3970 47926
(.branch 3969 47925
(.branch 3968 32043
.empty
.empty)
.empty)
(.branch 3971 32091
.empty
.empty))
(.branch 3974 47598
(.branch 3973 47597
.empty
.empty)
(.branch 3975 30617
.empty
.empty)))))
(.branch 3994 48642
(.branch 3985 47953
(.branch 3981 47961
(.branch 3979 30630
(.branch 3978 47650
(.branch 3977 47649
.empty
.empty)
.empty)
(.branch 3980 32052
.empty
.empty))
(.branch 3983 32100
(.branch 3982 47962
.empty
.empty)
(.branch 3984 32050
.empty
.empty)))
(.branch 3990 47626
(.branch 3988 30576
(.branch 3987 32098
(.branch 3986 47954
.empty
.empty)
.empty)
(.branch 3989 47625
.empty
.empty))
(.branch 3992 25262
(.branch 3991 30624
.empty
.empty)
(.branch 3993 48641
.empty
.empty))))
(.branch 4003 27034
(.branch 3999 27036
(.branch 3997 48953
(.branch 3996 26988
(.branch 3995 25310
.empty
.empty)
.empty)
(.branch 3998 48954
.empty
.empty))
(.branch 4001 48945
(.branch 4000 26986
.empty
.empty)
(.branch 4002 48946
.empty
.empty)))
(.branch 4007 25304
(.branch 4005 48617
(.branch 4004 25256
.empty
.empty)
(.branch 4006 48618
.empty
.empty))
(.branch 4009 48677
(.branch 4008 25271
.empty
.empty)
(.branch 4010 48678
.empty
.empty)))))))))
(.branch 4298 87806
(.branch 4155 94071
(.branch 4083 86017
(.branch 4047 32100
(.branch 4029 47933
(.branch 4020 25265
(.branch 4016 26995
(.branch 4014 48990
(.branch 4013 48989
(.branch 4012 26997
.empty
.empty)
.empty)
(.branch 4015 27045
.empty
.empty))
(.branch 4018 48982
(.branch 4017 48981
.empty
.empty)
(.branch 4019 27043
.empty
.empty)))
(.branch 4025 47621
(.branch 4023 25313
(.branch 4022 48654
(.branch 4021 48653
.empty
.empty)
.empty)
(.branch 4024 30575
.empty
.empty))
(.branch 4027 30623
(.branch 4026 47622
.empty
.empty)
(.branch 4028 32045
.empty
.empty))))
(.branch 4038 47598
(.branch 4034 47926
(.branch 4032 32043
(.branch 4031 32093
(.branch 4030 47934
.empty
.empty)
.empty)
(.branch 4033 47925
.empty
.empty))
(.branch 4036 30569
(.branch 4035 32091
.empty
.empty)
(.branch 4037 47597
.empty
.empty)))
(.branch 4043 30630
(.branch 4041 47649
(.branch 4040 30582
(.branch 4039 30617
.empty
.empty)
.empty)
(.branch 4042 47650
.empty
.empty))
(.branch 4045 47961
(.branch 4044 32052
.empty
.empty)
(.branch 4046 47962
.empty
.empty)))))
(.branch 4065 48945
(.branch 4056 25262
(.branch 4052 30576
(.branch 4050 47954
(.branch 4049 47953
(.branch 4048 32050
.empty
.empty)
.empty)
(.branch 4051 32098
.empty
.empty))
(.branch 4054 47626
(.branch 4053 47625
.empty
.empty)
(.branch 4055 30624
.empty
.empty)))
(.branch 4061 48953
(.branch 4059 25310
(.branch 4058 48642
(.branch 4057 48641
.empty
.empty)
.empty)
(.branch 4060 26988
.empty
.empty))
(.branch 4063 27036
(.branch 4062 48954
.empty
.empty)
(.branch 4064 26986
.empty
.empty))))
(.branch 4074 92271
(.branch 4070 48618
(.branch 4068 25256
(.branch 4067 27034
(.branch 4066 48946
.empty
.empty)
.empty)
(.branch 4069 48617
.empty
.empty))
(.branch 4072 88166
(.branch 4071 25304
.empty
.empty)
(.branch 4073 94407
.empty
.empty)))
(.branch 4079 86016
(.branch 4077 94393
(.branch 4076 88152
(.branch 4075 86030
.empty
.empty)
.empty)
(.branch 4078 92257
.empty
.empty))
(.branch 4081 94392
(.branch 4080 88153
.empty
.empty)
(.branch 4082 92256
.empty
.empty))))))
(.branch 4119 86078
(.branch 4101 86367
(.branch 4092 92401
(.branch 4088 92415
(.branch 4086 92270
(.branch 4085 94406
(.branch 4084 88167
.empty
.empty)
.empty)
(.branch 4087 86031
.empty
.empty))
(.branch 4090 88022
(.branch 4089 86366
.empty
.empty)
(.branch 4091 94071
.empty
.empty)))
(.branch 4097 86353
(.branch 4095 94057
(.branch 4094 88008
(.branch 4093 86352
.empty
.empty)
.empty)
(.branch 4096 92400
.empty
.empty))
(.branch 4099 94056
(.branch 4098 88009
.empty
.empty)
(.branch 4100 92414
.empty
.empty))))
(.branch 4110 92304
(.branch 4106 92318
(.branch 4104 88119
(.branch 4103 94070
(.branch 4102 88023
.empty
.empty)
.empty)
(.branch 4105 94358
.empty
.empty))
(.branch 4108 88105
(.branch 4107 86079
.empty
.empty)
(.branch 4109 94344
.empty
.empty)))
(.branch 4115 86064
(.branch 4113 94345
(.branch 4112 88104
(.branch 4111 86065
.empty
.empty)
.empty)
(.branch 4114 92305
.empty
.empty))
(.branch 4117 94359
(.branch 4116 88118
.empty
.empty)
(.branch 4118 92319
.empty
.empty)))))
(.branch 4137 94407
(.branch 4128 92353
(.branch 4124 92352
(.branch 4122 88071
(.branch 4121 86319
(.branch 4120 92366
.empty
.empty)
.empty)
(.branch 4123 94118
.empty
.empty))
(.branch 4126 88057
(.branch 4125 86305
.empty
.empty)
(.branch 4127 94104
.empty
.empty)))
(.branch 4133 86318
(.branch 4131 94105
(.branch 4130 88056
(.branch 4129 86304
.empty
.empty)
.empty)
(.branch 4132 92367
.empty
.empty))
(.branch 4135 94119
(.branch 4134 88070
.empty
.empty)
(.branch 4136 88166
.empty
.empty))))
(.branch 4146 92256
(.branch 4142 92257
(.branch 4140 88152
(.branch 4139 86030
(.branch 4138 92271
.empty
.empty)
.empty)
(.branch 4141 94393
.empty
.empty))
(.branch 4144 88153
(.branch 4143 86016
.empty
.empty)
(.branch 4145 94392
.empty
.empty)))
(.branch 4151 86031
(.branch 4149 94406
(.branch 4148 88167
(.branch 4147 86017
.empty
.empty)
.empty)
(.branch 4150 92270
.empty
.empty))
(.branch 4153 86366
(.branch 4152 92415
.empty
.empty)
(.branch 4154 88022
.empty
.empty)))))))
(.branch 4227 86664
(.branch 4191 94104
(.branch 4173 94344
(.branch 4164 92414
(.branch 4160 92400
(.branch 4158 88008
(.branch 4157 86352
(.branch 4156 92401
.empty
.empty)
.empty)
(.branch 4159 94057
.empty
.empty))
(.branch 4162 88009
(.branch 4161 86353
.empty
.empty)
(.branch 4163 94056
.empty
.empty)))
(.branch 4169 94358
(.branch 4167 94070
(.branch 4166 88023
(.branch 4165 86367
.empty
.empty)
.empty)
(.branch 4168 88119
.empty
.empty))
(.branch 4171 86079
(.branch 4170 92318
.empty
.empty)
(.branch 4172 88105
.empty
.empty))))
(.branch 4182 92319
(.branch 4178 92305
(.branch 4176 88104
(.branch 4175 86065
(.branch 4174 92304
.empty
.empty)
.empty)
(.branch 4177 94345
.empty
.empty))
(.branch 4180 88118
(.branch 4179 86064
.empty
.empty)
(.branch 4181 94359
.empty
.empty)))
(.branch 4187 94118
(.branch 4185 86319
(.branch 4184 92366
(.branch 4183 86078
.empty
.empty)
.empty)
(.branch 4186 88071
.empty
.empty))
(.branch 4189 86305
(.branch 4188 92352
.empty
.empty)
(.branch 4190 88057
.empty
.empty)))))
(.branch 4209 93696
(.branch 4200 87662
(.branch 4196 92367
(.branch 4194 88056
(.branch 4193 86304
(.branch 4192 92353
.empty
.empty)
.empty)
(.branch 4195 94105
.empty
.empty))
(.branch 4198 88070
(.branch 4197 86318
.empty
.empty)
(.branch 4199 94119
.empty
.empty)))
(.branch 4205 93697
(.branch 4203 86726
(.branch 4202 86438
(.branch 4201 87758
.empty
.empty)
.empty)
(.branch 4204 93985
.empty
.empty))
(.branch 4207 92665
(.branch 4206 92761
.empty
.empty)
(.branch 4208 93984
.empty
.empty))))
(.branch 4218 92726
(.branch 4214 86439
(.branch 4212 87663
(.branch 4211 92664
(.branch 4210 92760
.empty
.empty)
.empty)
(.branch 4213 87759
.empty
.empty))
(.branch 4216 94046
(.branch 4215 86727
.empty
.empty)
(.branch 4217 93758
.empty
.empty)))
(.branch 4223 86665
(.branch 4221 87793
(.branch 4220 87697
(.branch 4219 92630
.empty
.empty)
.empty)
(.branch 4222 86377
.empty
.empty))
(.branch 4225 87792
(.branch 4224 87696
.empty
.empty)
(.branch 4226 86376
.empty
.empty))))))
(.branch 4263 93999
(.branch 4245 86391
(.branch 4236 92617
(.branch 4232 86678
(.branch 4230 92727
(.branch 4229 93759
(.branch 4228 94047
.empty
.empty)
.empty)
(.branch 4231 92631
.empty
.empty))
(.branch 4234 87806
(.branch 4233 86390
.empty
.empty)
(.branch 4235 87710
.empty
.empty)))
(.branch 4241 92712
(.branch 4239 94033
(.branch 4238 93745
(.branch 4237 92713
.empty
.empty)
.empty)
(.branch 4240 92616
.empty
.empty))
(.branch 4243 94032
(.branch 4242 93744
.empty
.empty)
(.branch 4244 86679
.empty
.empty))))
(.branch 4254 87745
(.branch 4250 93710
(.branch 4248 92678
(.branch 4247 87711
(.branch 4246 87807
.empty
.empty)
.empty)
(.branch 4249 92774
.empty
.empty))
(.branch 4252 86713
(.branch 4251 93998
.empty
.empty)
(.branch 4253 86425
.empty
.empty)))
(.branch 4259 87648
(.branch 4257 86424
(.branch 4256 86712
(.branch 4255 87649
.empty
.empty)
.empty)
(.branch 4258 87744
.empty
.empty))
(.branch 4261 92775
(.branch 4260 92679
.empty
.empty)
(.branch 4262 93711
.empty
.empty)))))
(.branch 4281 93758
(.branch 4272 93984
(.branch 4268 93985
(.branch 4266 86438
(.branch 4265 87758
(.branch 4264 87662
.empty
.empty)
.empty)
(.branch 4267 86726
.empty
.empty))
(.branch 4270 92761
(.branch 4269 93697
.empty
.empty)
(.branch 4271 92665
.empty
.empty)))
(.branch 4277 87759
(.branch 4275 92664
(.branch 4274 92760
(.branch 4273 93696
.empty
.empty)
.empty)
(.branch 4276 87663
.empty
.empty))
(.branch 4279 86727
(.branch 4278 86439
.empty
.empty)
(.branch 4280 94046
.empty
.empty))))
(.branch 4290 86376
(.branch 4286 86377
(.branch 4284 87697
(.branch 4283 92630
(.branch 4282 92726
.empty
.empty)
.empty)
(.branch 4285 87793
.empty
.empty))
(.branch 4288 87696
(.branch 4287 86665
.empty
.empty)
(.branch 4289 87792
.empty
.empty)))
(.branch 4294 92727
(.branch 4292 94047
(.branch 4291 86664
.empty
.empty)
(.branch 4293 93759
.empty
.empty))
(.branch 4296 86678
(.branch 4295 92631
.empty
.empty)
(.branch 4297 86390
.empty
.empty))))))))
(.branch 4441 54326
(.branch 4370 60312
(.branch 4334 54313
(.branch 4316 86713
(.branch 4307 94032
(.branch 4303 94033
(.branch 4301 92713
(.branch 4300 92617
(.branch 4299 87710
.empty
.empty)
.empty)
(.branch 4302 93745
.empty
.empty))
(.branch 4305 92712
(.branch 4304 92616
.empty
.empty)
(.branch 4306 93744
.empty
.empty)))
(.branch 4312 92678
(.branch 4310 87807
(.branch 4309 86391
(.branch 4308 86679
.empty
.empty)
.empty)
(.branch 4311 87711
.empty
.empty))
(.branch 4314 93710
(.branch 4313 92774
.empty
.empty)
(.branch 4315 93998
.empty
.empty))))
(.branch 4325 92775
(.branch 4321 86424
(.branch 4319 87649
(.branch 4318 87745
(.branch 4317 86425
.empty
.empty)
.empty)
(.branch 4320 86712
.empty
.empty))
(.branch 4323 87648
(.branch 4322 87744
.empty
.empty)
(.branch 4324 92679
.empty
.empty)))
(.branch 4330 60278
(.branch 4328 60566
(.branch 4327 93999
(.branch 4326 93711
.empty
.empty)
.empty)
(.branch 4329 58622
.empty
.empty))
(.branch 4332 54217
(.branch 4331 58526
.empty
.empty)
(.branch 4333 52273
.empty
.empty)))))
(.branch 4352 52512
(.branch 4343 58527
(.branch 4339 52560
(.branch 4337 52272
(.branch 4336 54216
(.branch 4335 52561
.empty
.empty)
.empty)
(.branch 4338 54312
.empty
.empty))
(.branch 4341 58623
(.branch 4340 60567
.empty
.empty)
(.branch 4342 60279
.empty
.empty)))
(.branch 4348 52513
(.branch 4346 58574
(.branch 4345 60326
(.branch 4344 58478
.empty
.empty)
.empty)
(.branch 4347 60614
.empty
.empty))
(.branch 4350 52225
(.branch 4349 54361
.empty
.empty)
(.branch 4351 54265
.empty
.empty))))
(.branch 4361 52238
(.branch 4357 60327
(.branch 4355 54264
(.branch 4354 52224
(.branch 4353 54360
.empty
.empty)
.empty)
(.branch 4356 58479
.empty
.empty))
(.branch 4359 60615
(.branch 4358 58575
.empty
.empty)
(.branch 4360 54278
.empty
.empty)))
(.branch 4366 60313
(.branch 4364 60601
(.branch 4363 52526
(.branch 4362 54374
.empty
.empty)
.empty)
(.branch 4365 58561
.empty
.empty))
(.branch 4368 60600
(.branch 4367 58465
.empty
.empty)
(.branch 4369 58560
.empty
.empty))))))
(.branch 4406 60279
(.branch 4388 52575
(.branch 4379 54230
(.branch 4375 52527
(.branch 4373 52239
(.branch 4372 54279
(.branch 4371 58464
.empty
.empty)
.empty)
(.branch 4374 54375
.empty
.empty))
(.branch 4377 54326
(.branch 4376 52574
.empty
.empty)
(.branch 4378 52286
.empty
.empty)))
(.branch 4384 58512
(.branch 4382 58609
(.branch 4381 60265
(.branch 4380 58513
.empty
.empty)
.empty)
(.branch 4383 60553
.empty
.empty))
(.branch 4386 58608
(.branch 4385 60264
.empty
.empty)
(.branch 4387 60552
.empty
.empty))))
(.branch 4397 52273
(.branch 4393 58622
(.branch 4391 54231
(.branch 4390 52287
(.branch 4389 54327
.empty
.empty)
.empty)
(.branch 4392 60566
.empty
.empty))
(.branch 4395 58526
(.branch 4394 60278
.empty
.empty)
(.branch 4396 54217
.empty
.empty)))
(.branch 4402 54312
(.branch 4400 54216
(.branch 4399 52561
(.branch 4398 54313
.empty
.empty)
.empty)
(.branch 4401 52272
.empty
.empty))
(.branch 4404 60567
(.branch 4403 52560
.empty
.empty)
(.branch 4405 58623
.empty
.empty)))))
(.branch 4424 54278
(.branch 4415 54265
(.branch 4411 60614
(.branch 4409 60326
(.branch 4408 58478
(.branch 4407 58527
.empty
.empty)
.empty)
(.branch 4410 58574
.empty
.empty))
(.branch 4413 54361
(.branch 4412 52513
.empty
.empty)
(.branch 4414 52225
.empty
.empty)))
(.branch 4420 58479
(.branch 4418 52224
(.branch 4417 54360
(.branch 4416 52512
.empty
.empty)
.empty)
(.branch 4419 54264
.empty
.empty))
(.branch 4422 58575
(.branch 4421 60327
.empty
.empty)
(.branch 4423 60615
.empty
.empty))))
(.branch 4433 58560
(.branch 4429 58561
(.branch 4427 52526
(.branch 4426 54374
(.branch 4425 52238
.empty
.empty)
.empty)
(.branch 4428 60601
.empty
.empty))
(.branch 4431 58465
(.branch 4430 60313
.empty
.empty)
(.branch 4432 60600
.empty
.empty)))
(.branch 4437 52239
(.branch 4435 58464
(.branch 4434 60312
.empty
.empty)
(.branch 4436 54279
.empty
.empty))
(.branch 4439 52527
(.branch 4438 54375
.empty
.empty)
(.branch 4440 52574
.empty
.empty)))))))
(.branch 4513 54289
(.branch 4477 52536
(.branch 4459 54398
(.branch 4450 58608
(.branch 4446 58609
(.branch 4444 58513
(.branch 4443 54230
(.branch 4442 52286
.empty
.empty)
.empty)
(.branch 4445 60265
.empty
.empty))
(.branch 4448 58512
(.branch 4447 60553
.empty
.empty)
(.branch 4449 60264
.empty
.empty)))
(.branch 4455 54231
(.branch 4453 54327
(.branch 4452 52575
(.branch 4451 60552
.empty
.empty)
.empty)
(.branch 4454 52287
.empty
.empty))
(.branch 4457 52502
(.branch 4456 52214
.empty
.empty)
(.branch 4458 54302
.empty
.empty))))
(.branch 4468 52215
(.branch 4464 58537
(.branch 4462 60624
(.branch 4461 58440
(.branch 4460 58536
.empty
.empty)
.empty)
(.branch 4463 60336
.empty
.empty))
(.branch 4466 60625
(.branch 4465 58441
.empty
.empty)
(.branch 4467 60337
.empty
.empty)))
(.branch 4473 58502
(.branch 4471 54399
(.branch 4470 54303
(.branch 4469 52503
.empty
.empty)
.empty)
(.branch 4472 58598
.empty
.empty))
(.branch 4475 60302
(.branch 4474 60590
.empty
.empty)
(.branch 4476 52248
.empty
.empty)))))
(.branch 4495 58584
(.branch 4486 60591
(.branch 4482 54241
(.branch 4480 52249
(.branch 4479 54336
(.branch 4478 54240
.empty
.empty)
.empty)
(.branch 4481 52537
.empty
.empty))
(.branch 4484 58599
(.branch 4483 54337
.empty
.empty)
(.branch 4485 58503
.empty
.empty)))
(.branch 4491 52262
(.branch 4489 54254
(.branch 4488 54350
(.branch 4487 60303
.empty
.empty)
.empty)
(.branch 4490 52550
.empty
.empty))
(.branch 4493 60576
(.branch 4492 60288
.empty
.empty)
(.branch 4494 58488
.empty
.empty))))
(.branch 4504 60350
(.branch 4500 54351
(.branch 4498 58489
(.branch 4497 60577
(.branch 4496 60289
.empty
.empty)
.empty)
(.branch 4499 58585
.empty
.empty))
(.branch 4502 52551
(.branch 4501 54255
.empty
.empty)
(.branch 4503 52263
.empty
.empty)))
(.branch 4509 54288
(.branch 4507 58550
(.branch 4506 58454
(.branch 4505 60638
.empty
.empty)
.empty)
(.branch 4508 54384
.empty
.empty))
(.branch 4511 52200
(.branch 4510 52488
.empty
.empty)
(.branch 4512 54385
.empty
.empty))))))
(.branch 4549 58503
(.branch 4531 60337
(.branch 4522 54302
(.branch 4518 58455
(.branch 4516 60351
(.branch 4515 52201
(.branch 4514 52489
.empty
.empty)
.empty)
(.branch 4517 60639
.empty
.empty))
(.branch 4520 52214
(.branch 4519 58551
.empty
.empty)
(.branch 4521 52502
.empty
.empty)))
(.branch 4527 60336
(.branch 4525 58440
(.branch 4524 58536
(.branch 4523 54398
.empty
.empty)
.empty)
(.branch 4526 60624
.empty
.empty))
(.branch 4529 58441
(.branch 4528 58537
.empty
.empty)
(.branch 4530 60625
.empty
.empty))))
(.branch 4540 52248
(.branch 4536 58598
(.branch 4534 54303
(.branch 4533 52503
(.branch 4532 52215
.empty
.empty)
.empty)
(.branch 4535 54399
.empty
.empty))
(.branch 4538 60590
(.branch 4537 58502
.empty
.empty)
(.branch 4539 60302
.empty
.empty)))
(.branch 4545 52537
(.branch 4543 54336
(.branch 4542 54240
(.branch 4541 52536
.empty
.empty)
.empty)
(.branch 4544 52249
.empty
.empty))
(.branch 4547 54337
(.branch 4546 54241
.empty
.empty)
(.branch 4548 58599
.empty
.empty)))))
(.branch 4567 52263
(.branch 4558 58488
(.branch 4554 52550
(.branch 4552 54350
(.branch 4551 60303
(.branch 4550 60591
.empty
.empty)
.empty)
(.branch 4553 54254
.empty
.empty))
(.branch 4556 60288
(.branch 4555 52262
.empty
.empty)
(.branch 4557 60576
.empty
.empty)))
(.branch 4563 58585
(.branch 4561 60577
(.branch 4560 60289
(.branch 4559 58584
.empty
.empty)
.empty)
(.branch 4562 58489
.empty
.empty))
(.branch 4565 54255
(.branch 4564 54351
.empty
.empty)
(.branch 4566 52551
.empty
.empty))))
(.branch 4576 54385
(.branch 4572 54384
(.branch 4570 58454
(.branch 4569 60638
(.branch 4568 60350
.empty
.empty)
.empty)
(.branch 4571 58550
.empty
.empty))
(.branch 4574 52488
(.branch 4573 54288
.empty
.empty)
(.branch 4575 52200
.empty
.empty)))
(.branch 4580 60351
(.branch 4578 52489
(.branch 4577 54289
.empty
.empty)
(.branch 4579 52201
.empty
.empty))
(.branch 4582 58455
(.branch 4581 60639
.empty
.empty)
(.branch 4583 58551
.empty
.empty))))))))))))

/-- Bounded lookup of the complete candidate original source labels for frame 2. -/
def generatedAxisGlobalOddFourthSelectedSourceTree02 : GeneratedAxisGlobalSparseLookupTree (Fin 98280) :=
  (.branch 2292 1108
(.branch 1146 13332
(.branch 573 1016
(.branch 286 33088
(.branch 143 1014
(.branch 71 713
(.branch 35 598
(.branch 17 277
(.branch 8 33103
(.branch 4 33120
(.branch 2 33024
(.branch 1 33248
(.branch 0 32960
.empty
.empty)
.empty)
(.branch 3 33152
.empty
.empty))
(.branch 6 33135
(.branch 5 33167
.empty
.empty)
(.branch 7 33184
.empty
.empty)))
(.branch 13 33040
(.branch 11 32975
(.branch 10 33087
(.branch 9 33072
.empty
.empty)
.empty)
(.branch 12 45
.empty
.empty))
(.branch 15 33007
(.branch 14 33200
.empty
.empty)
(.branch 16 32943
.empty
.empty))))
(.branch 26 678
(.branch 22 2
(.branch 20 32992
(.branch 19 33216
(.branch 18 33232
.empty
.empty)
.empty)
(.branch 21 33055
.empty
.empty))
(.branch 24 582
(.branch 23 1152
.empty
.empty)
(.branch 25 838
.empty
.empty)))
(.branch 31 630
(.branch 29 870
(.branch 28 809
(.branch 27 841
.empty
.empty)
.empty)
(.branch 30 649
.empty
.empty))
(.branch 33 461
(.branch 32 633
.empty
.empty)
(.branch 34 32956
.empty
.empty)))))
(.branch 53 959
(.branch 44 32953
(.branch 40 1157
(.branch 38 448
(.branch 37 553
(.branch 36 1155
.empty
.empty)
.empty)
(.branch 39 32965
.empty
.empty))
(.branch 42 447
(.branch 41 1158
.empty
.empty)
(.branch 43 601
.empty
.empty)))
(.branch 49 751
(.branch 47 992
(.branch 46 768
(.branch 45 1088
.empty
.empty)
.empty)
(.branch 48 783
.empty
.empty))
(.branch 51 975
(.branch 50 800
.empty
.empty)
(.branch 52 944
.empty
.empty))))
(.branch 62 381
(.branch 58 1071
(.branch 56 1104
(.branch 55 33244
(.branch 54 1167
.empty
.empty)
.empty)
(.branch 57 362
.empty
.empty))
(.branch 60 33253
(.branch 59 1135
.empty
.empty)
(.branch 61 363
.empty
.empty)))
(.branch 67 742
(.branch 65 33241
(.branch 64 1119
(.branch 63 1184
.empty
.empty)
.empty)
(.branch 66 902
.empty
.empty))
(.branch 69 873
(.branch 68 905
.empty
.empty)
(.branch 70 934
.empty
.empty))))))
(.branch 107 1056
(.branch 89 549
(.branch 80 33029
(.branch 76 210
(.branch 74 570
(.branch 73 697
(.branch 72 694
.empty
.empty)
.empty)
(.branch 75 33020
.empty
.empty))
(.branch 78 498
(.branch 77 1091
.empty
.empty)
(.branch 79 572
.empty
.empty)))
(.branch 85 33017
(.branch 83 576
(.branch 82 1094
(.branch 81 1093
.empty
.empty)
.empty)
(.branch 84 212
.empty
.empty))
(.branch 87 551
(.branch 86 1024
.empty
.empty)
(.branch 88 550
.empty
.empty))))
(.branch 98 828
(.branch 94 33148
(.branch 92 1017
(.branch 91 1027
(.branch 90 1018
.empty
.empty)
.empty)
(.branch 93 826
.empty
.empty))
(.branch 96 771
(.branch 95 901
.empty
.empty)
(.branch 97 892
.empty
.empty)))
(.branch 103 895
(.branch 101 774
(.branch 100 773
(.branch 99 33157
.empty
.empty)
.empty)
(.branch 102 832
.empty
.empty))
(.branch 105 1039
(.branch 104 33145
.empty
.empty)
(.branch 106 1007
.empty
.empty)))))
(.branch 125 1045
(.branch 116 668
(.branch 112 33116
(.branch 110 250
(.branch 109 524
(.branch 108 256
.empty
.empty)
.empty)
(.branch 111 666
.empty
.empty))
(.branch 114 995
(.branch 113 741
.empty
.empty)
(.branch 115 732
.empty
.empty)))
(.branch 121 735
(.branch 119 998
(.branch 118 997
(.branch 117 33125
.empty
.empty)
.empty)
(.branch 120 672
.empty
.empty))
(.branch 123 273
(.branch 122 33113
.empty
.empty)
(.branch 124 274
.empty
.empty))))
(.branch 134 33162
(.branch 130 906
(.branch 128 853
(.branch 127 1046
(.branch 126 1036
.empty
.empty)
.empty)
(.branch 129 33171
.empty
.empty))
(.branch 132 915
(.branch 131 780
.empty
.empty)
(.branch 133 851
.empty
.empty)))
(.branch 139 33174
(.branch 137 847
(.branch 136 777
(.branch 135 778
.empty
.empty)
.empty)
(.branch 138 912
.empty
.empty))
(.branch 141 1013
(.branch 140 275
.empty
.empty)
(.branch 142 1004
.empty
.empty)))))))
(.branch 215 32970
(.branch 179 33098
(.branch 161 933
(.branch 152 745
(.branch 148 883
(.branch 146 874
(.branch 145 33139
(.branch 144 821
.empty
.empty)
.empty)
(.branch 147 748
.empty
.empty))
(.branch 150 33130
(.branch 149 819
.empty
.empty)
(.branch 151 746
.empty
.empty)))
(.branch 157 1059
(.branch 155 33142
(.branch 154 880
(.branch 153 815
.empty
.empty)
.empty)
(.branch 156 1050
.empty
.empty))
(.branch 159 858
(.branch 158 1049
.empty
.empty)
(.branch 160 33180
.empty
.empty))))
(.branch 170 33177
(.branch 166 805
(.branch 164 860
(.branch 163 924
(.branch 162 803
.empty
.empty)
.empty)
(.branch 165 33189
.empty
.empty))
(.branch 168 864
(.branch 167 806
.empty
.empty)
(.branch 169 927
.empty
.empty)))
(.branch 175 714
(.branch 173 661
(.branch 172 248
(.branch 171 526
.empty
.empty)
.empty)
(.branch 174 33107
.empty
.empty))
(.branch 177 723
(.branch 176 972
.empty
.empty)
(.branch 178 659
.empty
.empty)))))
(.branch 197 33065
(.branch 188 693
(.branch 184 33110
(.branch 182 655
(.branch 181 969
(.branch 180 970
.empty
.empty)
.empty)
(.branch 183 720
.empty
.empty))
(.branch 186 618
(.branch 185 532
.empty
.empty)
(.branch 187 33068
.empty
.empty)))
(.branch 193 949
(.branch 191 620
(.branch 190 684
(.branch 189 947
.empty
.empty)
.empty)
(.branch 192 33077
.empty
.empty))
(.branch 195 624
(.branch 194 950
.empty
.empty)
(.branch 196 687
.empty
.empty))))
(.branch 206 953
(.branch 202 707
(.branch 200 698
(.branch 199 33091
(.branch 198 645
.empty
.empty)
.empty)
(.branch 201 956
.empty
.empty))
(.branch 204 33082
(.branch 203 643
.empty
.empty)
(.branch 205 954
.empty
.empty)))
(.branch 211 586
(.branch 209 33094
(.branch 208 704
(.branch 207 639
.empty
.empty)
.empty)
(.branch 210 32979
.empty
.empty))
(.branch 213 565
(.branch 212 1164
.empty
.empty)
(.branch 214 171
.empty
.empty))))))
(.branch 251 1065
(.branch 233 588
(.branch 224 32947
(.branch 220 32982
(.branch 218 172
(.branch 217 1161
(.branch 216 1162
.empty
.empty)
.empty)
(.branch 219 613
.empty
.empty))
(.branch 222 33196
(.branch 221 33036
.empty
.empty)
(.branch 223 33011
.empty
.empty)))
(.branch 229 33059
(.branch 227 33212
(.branch 226 33228
(.branch 225 278
.empty
.empty)
.empty)
(.branch 228 32988
.empty
.empty))
(.branch 231 1107
(.branch 230 1
.empty
.empty)
(.branch 232 488
.empty
.empty))))
(.branch 242 33205
(.branch 238 222
(.branch 236 1110
(.branch 235 1109
(.branch 234 33045
.empty
.empty)
.empty)
(.branch 237 592
.empty
.empty))
(.branch 240 1068
(.branch 239 33033
.empty
.empty)
(.branch 241 1132
.empty
.empty)))
(.branch 247 33193
(.branch 245 1187
(.branch 244 87
(.branch 243 105
.empty
.empty)
.empty)
(.branch 246 1116
.empty
.empty))
(.branch 249 33002
(.branch 248 563
.empty
.empty)
(.branch 250 1066
.empty
.empty)))))
(.branch 269 33225
(.branch 260 32950
(.branch 256 1130
(.branch 254 33014
(.branch 253 486
(.branch 252 559
.empty
.empty)
.empty)
(.branch 255 32938
.empty
.empty))
(.branch 258 185
(.branch 257 1129
.empty
.empty)
(.branch 259 611
.empty
.empty)))
(.branch 265 321
(.branch 263 32997
(.branch 262 33221
(.branch 261 33237
.empty
.empty)
.empty)
(.branch 264 33050
.empty
.empty))
(.branch 267 1189
(.branch 266 86
.empty
.empty)
(.branch 268 1114
.empty
.empty))))
(.branch 278 33023
(.branch 274 32985
(.branch 272 33209
(.branch 271 1113
(.branch 270 1190
.empty
.empty)
.empty)
(.branch 273 607
.empty
.empty))
(.branch 276 32959
(.branch 275 33062
.empty
.empty)
(.branch 277 33247
.empty
.empty)))
(.branch 282 33136
(.branch 280 33119
(.branch 279 33151
.empty
.empty)
(.branch 281 33168
.empty
.empty))
(.branch 284 33104
(.branch 283 33183
.empty
.empty)
(.branch 285 33071
.empty
.empty))))))))
(.branch 430 879
(.branch 358 1081
(.branch 322 767
(.branch 304 822
(.branch 295 33215
(.branch 291 33008
(.branch 289 33039
(.branch 288 276
(.branch 287 32976
.empty
.empty)
.empty)
(.branch 290 33199
.empty
.empty))
(.branch 293 24
(.branch 292 32944
.empty
.empty)
(.branch 294 33231
.empty
.empty)))
(.branch 300 569
(.branch 298 299
(.branch 297 33056
(.branch 296 32991
.empty
.empty)
.empty)
(.branch 299 1151
.empty
.empty))
(.branch 302 665
(.branch 301 825
.empty
.empty)
(.branch 303 854
.empty
.empty))))
(.branch 313 566
(.branch 309 156
(.branch 307 617
(.branch 306 662
(.branch 305 857
.empty
.empty)
.empty)
(.branch 308 646
.empty
.empty))
(.branch 311 585
(.branch 310 32963
.empty
.empty)
(.branch 312 1148
.empty
.empty)))
(.branch 318 158
(.branch 316 1146
(.branch 315 32954
(.branch 314 157
.empty
.empty)
.empty)
(.branch 317 1145
.empty
.empty))
(.branch 320 32966
(.branch 319 614
.empty
.empty)
(.branch 321 1087
.empty
.empty)))))
(.branch 340 1120
(.branch 331 33251
(.branch 327 976
(.branch 325 752
(.branch 324 784
(.branch 323 991
.empty
.empty)
.empty)
(.branch 326 799
.empty
.empty))
(.branch 329 960
(.branch 328 943
.empty
.empty)
(.branch 330 1168
.empty
.empty)))
(.branch 336 33242
(.branch 334 1072
(.branch 333 123
(.branch 332 1103
.empty
.empty)
.empty)
(.branch 335 1136
.empty
.empty))
(.branch 338 88
(.branch 337 106
.empty
.empty)
(.branch 339 1183
.empty
.empty))))
(.branch 349 710
(.branch 345 886
(.branch 343 729
(.branch 342 889
(.branch 341 33254
.empty
.empty)
.empty)
(.branch 344 918
.empty
.empty))
(.branch 347 726
(.branch 346 921
.empty
.empty)
(.branch 348 681
.empty
.empty)))
(.branch 354 211
(.branch 352 507
(.branch 351 33027
(.branch 350 581
.empty
.empty)
.empty)
(.branch 353 1084
.empty
.empty))
(.branch 356 33018
(.branch 355 579
.empty
.empty)
(.branch 357 1082
.empty
.empty))))))
(.branch 394 986
(.branch 376 762
(.branch 367 1020
(.branch 363 270
(.branch 361 33030
(.branch 360 497
(.branch 359 575
.empty
.empty)
.empty)
(.branch 362 1023
.empty
.empty))
(.branch 365 272
(.branch 364 271
.empty
.empty)
(.branch 366 1029
.empty
.empty)))
(.branch 372 764
(.branch 370 33155
(.branch 369 837
(.branch 368 1030
.empty
.empty)
.empty)
(.branch 371 890
.empty
.empty))
(.branch 374 835
(.branch 373 899
.empty
.empty)
(.branch 375 33146
.empty
.empty))))
(.branch 385 261
(.branch 381 1040
(.branch 379 896
(.branch 378 831
(.branch 377 761
.empty
.empty)
.empty)
(.branch 380 33158
.empty
.empty))
(.branch 383 1055
(.branch 382 1008
.empty
.empty)
(.branch 384 525
.empty
.empty)))
(.branch 390 988
(.branch 388 33123
(.branch 387 677
(.branch 386 531
.empty
.empty)
.empty)
(.branch 389 730
.empty
.empty))
(.branch 392 675
(.branch 391 739
.empty
.empty)
(.branch 393 33114
.empty
.empty)))))
(.branch 412 790
(.branch 403 1033
(.branch 399 548
(.branch 397 736
(.branch 396 671
(.branch 395 985
.empty
.empty)
.empty)
(.branch 398 33126
.empty
.empty))
(.branch 401 1034
(.branch 400 547
.empty
.empty)
(.branch 402 1043
.empty
.empty)))
(.branch 408 908
(.branch 406 917
(.branch 405 33164
(.branch 404 842
.empty
.empty)
.empty)
(.branch 407 787
.empty
.empty))
(.branch 410 33173
(.branch 409 844
.empty
.empty)
(.branch 411 789
.empty
.empty))))
(.branch 421 33132
(.branch 417 1002
(.branch 415 33161
(.branch 414 911
(.branch 413 848
.empty
.empty)
.empty)
(.branch 416 546
.empty
.empty))
(.branch 419 1001
(.branch 418 1011
.empty
.empty)
(.branch 420 810
.empty
.empty)))
(.branch 426 33141
(.branch 424 876
(.branch 423 755
(.branch 422 885
.empty
.empty)
.empty)
(.branch 425 812
.empty
.empty))
(.branch 428 758
(.branch 427 757
.empty
.empty)
(.branch 429 816
.empty
.empty)))))))
(.branch 502 33235
(.branch 466 691
(.branch 448 537
(.branch 439 931
(.branch 435 869
(.branch 433 1052
(.branch 432 1061
(.branch 431 33129
.empty
.empty)
.empty)
(.branch 434 1062
.empty
.empty))
(.branch 437 922
(.branch 436 33187
.empty
.empty)
(.branch 438 796
.empty
.empty)))
(.branch 444 863
(.branch 442 794
(.branch 441 33178
(.branch 440 867
.empty
.empty)
.empty)
(.branch 443 793
.empty
.empty))
(.branch 446 33190
(.branch 445 928
.empty
.empty)
(.branch 447 255
.empty
.empty))))
(.branch 457 982
(.branch 453 716
(.branch 451 725
(.branch 450 33100
(.branch 449 650
.empty
.empty)
.empty)
(.branch 452 979
.empty
.empty))
(.branch 455 33109
(.branch 454 652
.empty
.empty)
(.branch 456 981
.empty
.empty)))
(.branch 462 629
(.branch 460 33097
(.branch 459 719
(.branch 458 656
.empty
.empty)
.empty)
(.branch 461 249
.empty
.empty))
(.branch 464 682
(.branch 463 33075
.empty
.empty)
(.branch 465 940
.empty
.empty)))))
(.branch 484 703
(.branch 475 33084
(.branch 471 623
(.branch 469 938
(.branch 468 33066
(.branch 467 627
.empty
.empty)
.empty)
(.branch 470 937
.empty
.empty))
(.branch 473 33078
(.branch 472 688
.empty
.empty)
(.branch 474 634
.empty
.empty)))
(.branch 480 33093
(.branch 478 700
(.branch 477 963
(.branch 476 709
.empty
.empty)
.empty)
(.branch 479 636
.empty
.empty))
(.branch 482 966
(.branch 481 965
.empty
.empty)
(.branch 483 640
.empty
.empty))))
(.branch 493 1174
(.branch 489 554
(.branch 487 597
(.branch 486 32972
(.branch 485 33081
.empty
.empty)
.empty)
(.branch 488 1171
.empty
.empty))
(.branch 491 32981
(.branch 490 434
.empty
.empty)
(.branch 492 1173
.empty
.empty)))
(.branch 498 33203
(.branch 496 32969
(.branch 495 602
(.branch 494 433
.empty
.empty)
.empty)
(.branch 497 33043
.empty
.empty))
(.branch 500 32940
(.branch 499 33004
.empty
.empty)
(.branch 501 23
.empty
.empty))))))
(.branch 538 33210
(.branch 520 382
(.branch 511 1098
(.branch 507 1100
(.branch 505 33052
(.branch 504 32995
(.branch 503 33219
.empty
.empty)
.empty)
(.branch 506 300
.empty
.empty))
(.branch 509 595
(.branch 508 221
.empty
.empty)
(.branch 510 33034
.empty
.empty)))
(.branch 516 1075
(.branch 514 487
(.branch 513 591
(.branch 512 1097
.empty
.empty)
.empty)
(.branch 515 33046
.empty
.empty))
(.branch 518 33194
(.branch 517 1139
.empty
.empty)
(.branch 519 364
.empty
.empty))))
(.branch 529 231
(.branch 525 33013
(.branch 523 33206
(.branch 522 1123
(.branch 521 1180
.empty
.empty)
.empty)
(.branch 524 556
.empty
.empty))
(.branch 527 1078
(.branch 526 1077
.empty
.empty)
(.branch 528 560
.empty
.empty)))
(.branch 534 432
(.branch 532 1141
(.branch 531 32949
(.branch 530 33001
.empty
.empty)
.empty)
(.branch 533 1142
.empty
.empty))
(.branch 536 32937
(.branch 535 604
.empty
.empty)
(.branch 537 33226
.empty
.empty)))))
(.branch 556 1063
(.branch 547 1126
(.branch 543 1178
(.branch 541 0
(.branch 540 33061
(.branch 539 32986
.empty
.empty)
.empty)
(.branch 542 399
.empty
.empty))
(.branch 545 33238
(.branch 544 1125
.empty
.empty)
(.branch 546 1177
.empty
.empty)))
(.branch 552 538
(.branch 550 32998
(.branch 549 608
(.branch 548 33222
.empty
.empty)
.empty)
(.branch 551 33049
.empty
.empty))
(.branch 554 542
(.branch 553 1000
.empty
.empty)
(.branch 555 1003
.empty
.empty))))
(.branch 565 1047
(.branch 561 540
(.branch 559 543
(.branch 558 1060
(.branch 557 539
.empty
.empty)
.empty)
(.branch 560 1031
.empty
.empty))
(.branch 563 544
(.branch 562 1028
.empty
.empty)
(.branch 564 265
.empty
.empty)))
(.branch 569 541
(.branch 567 1044
(.branch 566 269
.empty
.empty)
(.branch 568 1032
.empty
.empty))
(.branch 571 545
(.branch 570 1035
.empty
.empty)
(.branch 572 264
.empty
.empty)))))))))
(.branch 860 10181
(.branch 717 13348
(.branch 645 37783
(.branch 609 1057
(.branch 591 252
(.branch 582 1012
(.branch 578 267
(.branch 576 263
(.branch 575 1019
(.branch 574 268
.empty
.empty)
.empty)
(.branch 577 1048
.empty
.empty))
(.branch 580 1015
(.branch 579 1051
.empty
.empty)
(.branch 581 262
.empty
.empty)))
(.branch 587 1005
(.branch 585 1009
(.branch 584 533
(.branch 583 266
.empty
.empty)
.empty)
(.branch 586 251
.empty
.empty))
(.branch 589 534
(.branch 588 1054
.empty
.empty)
(.branch 590 1058
.empty
.empty))))
(.branch 600 1041
(.branch 596 260
(.branch 594 1026
(.branch 593 535
(.branch 592 1022
.empty
.empty)
.empty)
(.branch 595 253
.empty
.empty))
(.branch 598 530
(.branch 597 1038
.empty
.empty)
(.branch 599 1042
.empty
.empty)))
(.branch 605 1025
(.branch 603 254
(.branch 602 1037
(.branch 601 536
.empty
.empty)
.empty)
(.branch 604 259
.empty
.empty))
(.branch 607 1021
(.branch 606 529
.empty
.empty)
(.branch 608 258
.empty
.empty)))))
(.branch 627 13233
(.branch 618 37727
(.branch 614 1010
(.branch 612 1006
(.branch 611 1053
(.branch 610 528
.empty
.empty)
.empty)
(.branch 613 257
.empty
.empty))
(.branch 616 13309
(.branch 615 527
.empty
.empty)
(.branch 617 13310
.empty
.empty)))
(.branch 623 13402
(.branch 621 37752
(.branch 620 37755
(.branch 619 37724
.empty
.empty)
.empty)
(.branch 622 13401
.empty
.empty))
(.branch 625 37651
(.branch 624 37648
.empty
.empty)
(.branch 626 13234
.empty
.empty))))
(.branch 636 13433
(.branch 632 37631
(.branch 630 37812
(.branch 629 13461
(.branch 628 13462
.empty
.empty)
.empty)
(.branch 631 37815
.empty
.empty))
(.branch 634 13277
(.branch 633 37628
.empty
.empty)
(.branch 635 13278
.empty
.empty)))
(.branch 641 13329
(.branch 639 37848
(.branch 638 37851
(.branch 637 13434
.empty
.empty)
.empty)
(.branch 640 13330
.empty
.empty))
(.branch 643 37683
(.branch 642 37680
.empty
.empty)
(.branch 644 37780
.empty
.empty))))))
(.branch 681 13243
(.branch 663 13445
(.branch 654 37771
(.branch 650 13325
(.branch 648 37679
(.branch 647 13365
(.branch 646 13366
.empty
.empty)
.empty)
(.branch 649 37676
.empty
.empty))
(.branch 652 13353
(.branch 651 13326
.empty
.empty)
(.branch 653 13354
.empty
.empty)))
(.branch 659 37635
(.branch 657 13281
(.branch 656 13282
(.branch 655 37768
.empty
.empty)
.empty)
(.branch 658 37632
.empty
.empty))
(.branch 661 37863
(.branch 660 37860
.empty
.empty)
(.branch 662 13446
.empty
.empty))))
(.branch 672 37728
(.branch 668 37803
(.branch 666 37647
(.branch 665 13230
(.branch 664 13229
.empty
.empty)
.empty)
(.branch 667 37644
.empty
.empty))
(.branch 670 13449
(.branch 669 37800
.empty
.empty)
(.branch 671 13450
.empty
.empty)))
(.branch 677 13413
(.branch 675 13313
(.branch 674 13314
(.branch 673 37731
.empty
.empty)
.empty)
(.branch 676 13414
.empty
.empty))
(.branch 679 37767
(.branch 678 37764
.empty
.empty)
(.branch 680 13339
.empty
.empty)))))
(.branch 699 37826
(.branch 690 37790
(.branch 686 37621
(.branch 684 13300
(.branch 683 37690
(.branch 682 37658
.empty
.empty)
.empty)
(.branch 685 13268
.empty
.empty))
(.branch 688 13471
(.branch 687 37717
.empty
.empty)
(.branch 689 13375
.empty
.empty)))
(.branch 695 37841
(.branch 693 13392
(.branch 692 13424
(.branch 691 37822
.empty
.empty)
.empty)
(.branch 694 37745
.empty
.empty))
(.branch 697 13379
(.branch 696 13475
.empty
.empty)
(.branch 698 37794
.empty
.empty))))
(.branch 708 13288
(.branch 704 13351
(.branch 702 37741
(.branch 701 13388
(.branch 700 13420
.empty
.empty)
.empty)
(.branch 703 37837
.empty
.empty))
(.branch 706 37670
(.branch 705 13255
.empty
.empty)
(.branch 707 37702
.empty
.empty)))
(.branch 713 13291
(.branch 711 37705
(.branch 710 37609
(.branch 709 13256
.empty
.empty)
.empty)
(.branch 712 13259
.empty
.empty))
(.branch 715 37610
(.branch 714 37706
.empty
.empty)
(.branch 716 13252
.empty
.empty)))))))
(.branch 789 10360
(.branch 753 34729
(.branch 735 37789
(.branch 726 37825
(.branch 722 37838
(.branch 720 13391
(.branch 719 37669
(.branch 718 37701
.empty
.empty)
.empty)
(.branch 721 13423
.empty
.empty))
(.branch 724 13376
(.branch 723 37742
.empty
.empty)
(.branch 725 13472
.empty
.empty)))
(.branch 731 37746
(.branch 729 13427
(.branch 728 13395
(.branch 727 37793
.empty
.empty)
.empty)
(.branch 730 37842
.empty
.empty))
(.branch 733 13468
(.branch 732 13372
.empty
.empty)
(.branch 734 37821
.empty
.empty))))
(.branch 744 34577
(.branch 740 13240
(.branch 738 37718
(.branch 737 13303
(.branch 736 13271
.empty
.empty)
.empty)
(.branch 739 37622
.empty
.empty))
(.branch 742 37689
(.branch 741 13336
.empty
.empty)
(.branch 743 37657
.empty
.empty)))
(.branch 749 34561
(.branch 747 34741
(.branch 746 34709
(.branch 745 34609
.empty
.empty)
.empty)
(.branch 748 34657
.empty
.empty))
(.branch 751 34693
(.branch 750 34789
.empty
.empty)
(.branch 752 34697
.empty
.empty)))))
(.branch 771 34658
(.branch 762 34682
(.branch 758 34653
(.branch 756 34777
(.branch 755 34605
(.branch 754 34573
.empty
.empty)
.empty)
(.branch 757 34681
.empty
.empty))
(.branch 760 34558
(.branch 759 34557
.empty
.empty)
(.branch 761 34654
.empty
.empty)))
(.branch 767 34698
(.branch 765 34574
(.branch 764 34606
(.branch 763 34778
.empty
.empty)
.empty)
(.branch 766 34730
.empty
.empty))
(.branch 769 34790
(.branch 768 34694
.empty
.empty)
(.branch 770 34562
.empty
.empty))))
(.branch 780 10208
(.branch 776 10256
(.branch 774 34610
(.branch 773 34710
(.branch 772 34742
.empty
.empty)
.empty)
(.branch 775 34578
.empty
.empty))
(.branch 778 10388
(.branch 777 10160
.empty
.empty)
(.branch 779 10292
.empty
.empty)))
(.branch 785 10280
(.branch 783 10372
(.branch 782 10340
(.branch 781 10240
.empty
.empty)
.empty)
(.branch 784 10376
.empty
.empty))
(.branch 787 10156
(.branch 786 10252
.empty
.empty)
(.branch 788 10328
.empty
.empty))))))
(.branch 825 10170
(.branch 807 10259
(.branch 798 10283
(.branch 794 10363
(.branch 792 10239
(.branch 791 10236
(.branch 790 10204
.empty
.empty)
.empty)
(.branch 793 10207
.empty
.empty))
(.branch 796 10159
(.branch 795 10331
.empty
.empty)
(.branch 797 10255
.empty
.empty)))
(.branch 803 10211
(.branch 801 10343
(.branch 800 10375
(.branch 799 10379
.empty
.empty)
.empty)
(.branch 802 10243
.empty
.empty))
(.branch 805 10391
(.branch 804 10295
.empty
.empty)
(.branch 806 10163
.empty
.empty))))
(.branch 816 34723
(.branch 812 10401
(.branch 810 34668
(.branch 809 10402
(.branch 808 34587
.empty
.empty)
.empty)
(.branch 811 10229
.empty
.empty))
(.branch 814 10230
(.branch 813 34584
.empty
.empty)
(.branch 815 34671
.empty
.empty)))
(.branch 821 34720
(.branch 819 10349
(.branch 818 34548
(.branch 817 10266
.empty
.empty)
.empty)
(.branch 820 10265
.empty
.empty))
(.branch 823 34551
(.branch 822 10350
.empty
.empty)
(.branch 824 34755
.empty
.empty)))))
(.branch 843 10217
(.branch 834 34764
(.branch 830 10318
(.branch 828 10169
(.branch 827 10317
(.branch 826 34644
.empty
.empty)
.empty)
(.branch 829 34752
.empty
.empty))
(.branch 832 34619
(.branch 831 34647
.empty
.empty)
(.branch 833 10306
.empty
.empty)))
(.branch 839 34767
(.branch 837 34616
(.branch 836 10305
(.branch 835 10197
.empty
.empty)
.empty)
(.branch 838 10198
.empty
.empty))
(.branch 841 10398
(.branch 840 34599
.empty
.empty)
(.branch 842 34672
.empty
.empty))))
(.branch 852 10277
(.branch 848 34719
(.branch 846 10218
(.branch 845 34596
(.branch 844 10397
.empty
.empty)
.empty)
(.branch 847 34675
.empty
.empty))
(.branch 850 34536
(.branch 849 10278
.empty
.empty)
(.branch 851 10353
.empty
.empty)))
(.branch 856 34751
(.branch 854 10354
(.branch 853 34716
.empty
.empty)
(.branch 855 34539
.empty
.empty))
(.branch 858 34632
(.branch 857 10182
.empty
.empty)
(.branch 859 10321
.empty
.empty))))))))
(.branch 1003 16438
(.branch 932 37849
(.branch 896 13280
(.branch 878 37754
(.branch 869 34628
(.branch 865 10302
(.branch 863 34635
(.branch 862 10322
(.branch 861 34748
.empty
.empty)
.empty)
(.branch 864 34631
.empty
.empty))
(.branch 867 10185
(.branch 866 34768
.empty
.empty)
(.branch 868 10301
.empty
.empty)))
(.branch 874 13435
(.branch 872 13311
(.branch 871 34771
(.branch 870 10186
.empty
.empty)
.empty)
(.branch 873 13279
.empty
.empty))
(.branch 876 37630
(.branch 875 13403
.empty
.empty)
(.branch 877 37726
.empty
.empty))))
(.branch 887 37813
(.branch 883 13364
(.branch 881 13232
(.branch 880 13328
(.branch 879 37850
.empty
.empty)
.empty)
(.branch 882 13460
.empty
.empty))
(.branch 885 37681
(.branch 884 37649
.empty
.empty)
(.branch 886 37781
.empty
.empty)))
(.branch 892 37678
(.branch 890 13355
(.branch 889 13327
(.branch 888 13231
.empty
.empty)
.empty)
(.branch 891 13451
.empty
.empty))
(.branch 894 37802
(.branch 893 37646
.empty
.empty)
(.branch 895 37770
.empty
.empty)))))
(.branch 914 13324
(.branch 905 13415
(.branch 901 37633
(.branch 899 13444
(.branch 898 13412
(.branch 897 13312
.empty
.empty)
.empty)
(.branch 900 37729
.empty
.empty))
(.branch 903 37765
(.branch 902 37861
.empty
.empty)
(.branch 904 13447
.empty
.empty)))
(.branch 910 37634
(.branch 908 37766
(.branch 907 13283
(.branch 906 13315
.empty
.empty)
.empty)
(.branch 909 37862
.empty
.empty))
(.branch 912 13448
(.branch 911 37730
.empty
.empty)
(.branch 913 13352
.empty
.empty))))
(.branch 923 13331
(.branch 919 37677
(.branch 917 37801
(.branch 916 37769
(.branch 915 13228
.empty
.empty)
.empty)
(.branch 918 37645
.empty
.empty))
(.branch 921 13463
(.branch 920 13367
.empty
.empty)
(.branch 922 13235
.empty
.empty)))
(.branch 928 13400
(.branch 926 37682
(.branch 925 37782
(.branch 924 37814
.empty
.empty)
.empty)
(.branch 927 37650
.empty
.empty))
(.branch 930 13276
(.branch 929 13432
.empty
.empty)
(.branch 931 13308
.empty
.empty))))))
(.branch 968 37795
(.branch 950 13258
(.branch 941 37688
(.branch 937 37792
(.branch 935 37629
(.branch 934 37725
(.branch 933 37753
.empty
.empty)
.empty)
(.branch 936 13337
.empty
.empty))
(.branch 939 37623
(.branch 938 13422
.empty
.empty)
(.branch 940 13377
.empty
.empty)))
(.branch 946 13426
(.branch 944 13349
(.branch 943 37839
(.branch 942 13270
.empty
.empty)
.empty)
(.branch 945 37788
.empty
.empty))
(.branch 948 13373
(.branch 947 37611
.empty
.empty)
(.branch 949 37700
.empty
.empty))))
(.branch 959 37719
(.branch 955 37743
(.branch 953 37656
(.branch 952 13473
(.branch 951 37843
.empty
.empty)
.empty)
(.branch 954 13302
.empty
.empty))
(.branch 957 37824
(.branch 956 13241
.empty
.empty)
(.branch 958 13390
.empty
.empty)))
(.branch 964 13253
(.branch 962 13290
(.branch 961 37668
(.branch 960 13469
.empty
.empty)
.empty)
(.branch 963 37747
.empty
.empty))
(.branch 966 13394
(.branch 965 37820
.empty
.empty)
(.branch 967 37707
.empty
.empty)))))
(.branch 986 37740
(.branch 977 13350
(.branch 973 13378
(.branch 971 13421
(.branch 970 37620
(.branch 969 13338
.empty
.empty)
.empty)
(.branch 972 37691
.empty
.empty))
(.branch 975 13269
(.branch 974 37836
.empty
.empty)
(.branch 976 37791
.empty
.empty)))
(.branch 982 37840
(.branch 980 37703
(.branch 979 13425
(.branch 978 37608
.empty
.empty)
.empty)
(.branch 981 13374
.empty
.empty))
(.branch 984 37659
(.branch 983 13257
.empty
.empty)
(.branch 985 13474
.empty
.empty))))
(.branch 995 13289
(.branch 991 13389
(.branch 989 13242
(.branch 988 37827
(.branch 987 13301
.empty
.empty)
.empty)
(.branch 990 37716
.empty
.empty))
(.branch 993 13470
(.branch 992 37671
.empty
.empty)
(.branch 994 37744
.empty
.empty)))
(.branch 999 13393
(.branch 997 13254
(.branch 996 37823
.empty
.empty)
(.branch 998 37704
.empty
.empty))
(.branch 1001 16521
(.branch 1000 16505
.empty
.empty)
(.branch 1002 16486
.empty
.empty)))))))
(.branch 1075 40813
(.branch 1039 40751
(.branch 1021 16522
(.branch 1012 40700
(.branch 1008 16301
(.branch 1006 40855
(.branch 1005 40920
(.branch 1004 40872
.empty
.empty)
.empty)
(.branch 1007 40839
.empty
.empty))
(.branch 1010 16402
(.branch 1009 16349
.empty
.empty)
(.branch 1011 16386
.empty
.empty)))
(.branch 1017 40923
(.branch 1015 40755
(.branch 1014 40803
(.branch 1013 40716
.empty
.empty)
.empty)
(.branch 1016 40875
.empty
.empty))
(.branch 1019 40836
(.branch 1018 40852
.empty
.empty)
(.branch 1020 16506
.empty
.empty))))
(.branch 1030 16401
(.branch 1026 40800
(.branch 1024 40703
(.branch 1023 16437
(.branch 1022 16485
.empty
.empty)
.empty)
(.branch 1025 40719
.empty
.empty))
(.branch 1028 16302
(.branch 1027 40752
.empty
.empty)
(.branch 1029 16350
.empty
.empty)))
(.branch 1035 16382
(.branch 1033 16353
(.branch 1032 16305
(.branch 1031 16385
.empty
.empty)
.empty)
(.branch 1034 16398
.empty
.empty))
(.branch 1037 40720
(.branch 1036 40704
.empty
.empty)
(.branch 1038 40799
.empty
.empty)))))
(.branch 1057 40935
(.branch 1048 40707
(.branch 1044 40884
(.branch 1042 16474
(.branch 1041 16533
(.branch 1040 16517
.empty
.empty)
.empty)
(.branch 1043 16426
.empty
.empty))
(.branch 1046 40843
(.branch 1045 40932
.empty
.empty)
(.branch 1047 40827
.empty
.empty)))
(.branch 1053 16354
(.branch 1051 40748
(.branch 1050 40796
(.branch 1049 40723
.empty
.empty)
.empty)
(.branch 1052 16306
.empty
.empty))
(.branch 1055 16381
(.branch 1054 16397
.empty
.empty)
(.branch 1056 40887
.empty
.empty))))
(.branch 1066 16547
(.branch 1062 16473
(.branch 1060 16518
(.branch 1059 40824
(.branch 1058 40840
.empty
.empty)
.empty)
(.branch 1061 16534
.empty
.empty))
(.branch 1064 16543
(.branch 1063 16425
.empty
.empty)
(.branch 1065 40742
.empty
.empty)))
(.branch 1071 40898
(.branch 1069 40894
(.branch 1068 16327
(.branch 1067 40730
.empty
.empty)
.empty)
(.branch 1070 16315
.empty
.empty))
(.branch 1073 40817
(.branch 1072 16360
.empty
.empty)
(.branch 1074 16372
.empty
.empty))))))
(.branch 1111 40861
(.branch 1093 40913
(.branch 1084 16447
(.branch 1080 16423
(.branch 1078 16460
(.branch 1077 40777
(.branch 1076 16464
.empty
.empty)
.empty)
(.branch 1079 40789
.empty
.empty))
(.branch 1082 16411
(.branch 1081 40862
.empty
.empty)
(.branch 1083 40866
.empty
.empty)))
(.branch 1089 40681
(.branch 1087 40762
(.branch 1086 16451
(.branch 1085 40774
.empty
.empty)
.empty)
(.branch 1088 16496
.empty
.empty))
(.branch 1091 40693
(.branch 1090 16492
.empty
.empty)
(.branch 1092 16328
.empty
.empty))))
(.branch 1102 16499
(.branch 1098 16331
(.branch 1096 16343
(.branch 1095 40909
(.branch 1094 16340
.empty
.empty)
.empty)
(.branch 1097 40910
.empty
.empty))
(.branch 1100 16495
(.branch 1099 40914
.empty
.empty)
(.branch 1101 40694
.empty
.empty)))
(.branch 1107 40773
(.branch 1105 40761
(.branch 1104 16448
(.branch 1103 40682
.empty
.empty)
.empty)
(.branch 1106 16444
.empty
.empty))
(.branch 1109 40865
(.branch 1108 16408
.empty
.empty)
(.branch 1110 16420
.empty
.empty)))))
(.branch 1129 13411
(.branch 1120 16312
(.branch 1116 16375
(.branch 1114 16467
(.branch 1113 40790
(.branch 1112 16463
.empty
.empty)
.empty)
(.branch 1115 40778
.empty
.empty))
(.branch 1118 16363
(.branch 1117 40814
.empty
.empty)
(.branch 1119 40818
.empty
.empty)))
(.branch 1125 40729
(.branch 1123 40893
(.branch 1122 16324
(.branch 1121 40897
.empty
.empty)
.empty)
(.branch 1124 16544
.empty
.empty))
(.branch 1127 40741
(.branch 1126 16540
.empty
.empty)
(.branch 1128 13307
.empty
.empty))))
(.branch 1138 13456
(.branch 1134 37653
(.branch 1132 37762
(.branch 1131 13236
(.branch 1130 13452
.empty
.empty)
.empty)
(.branch 1133 37722
.empty
.empty))
(.branch 1136 13319
(.branch 1135 37805
.empty
.empty)
(.branch 1137 13407
.empty
.empty)))
(.branch 1142 37641
(.branch 1140 37758
(.branch 1139 13224
.empty
.empty)
(.branch 1141 37734
.empty
.empty))
(.branch 1144 13443
(.branch 1143 37809
.empty
.empty)
(.branch 1145 13275
.empty
.empty))))))))))
(.branch 1719 452
(.branch 1433 77
(.branch 1290 16364
(.branch 1218 37828
(.branch 1182 37733
(.branch 1164 37674
(.branch 1155 13360
(.branch 1151 37685
(.branch 1149 37858
(.branch 1148 37626
(.branch 1147 13356
.empty
.empty)
.empty)
(.branch 1150 37773
.empty
.empty))
(.branch 1153 13287
(.branch 1152 13439
.empty
.empty)
(.branch 1154 13320
.empty
.empty)))
(.branch 1160 13363
(.branch 1158 37777
(.branch 1157 37854
(.branch 1156 37638
.empty
.empty)
.empty)
(.branch 1159 37673
.empty
.empty))
(.branch 1162 13284
(.branch 1161 13323
.empty
.empty)
(.branch 1163 13436
.empty
.empty))))
(.branch 1173 37774
(.branch 1169 13335
(.branch 1167 37637
(.branch 1166 37853
(.branch 1165 37778
.empty
.empty)
.empty)
(.branch 1168 13359
.empty
.empty))
(.branch 1171 13440
(.branch 1170 13272
.empty
.empty)
(.branch 1172 37686
.empty
.empty)))
(.branch 1178 13404
(.branch 1176 13227
(.branch 1175 37625
(.branch 1174 37857
.empty
.empty)
.empty)
(.branch 1177 13459
.empty
.empty))
(.branch 1180 37810
(.branch 1179 13316
.empty
.empty)
(.branch 1181 37642
.empty
.empty)))))
(.branch 1200 13250
(.branch 1191 37761
(.branch 1187 13304
(.branch 1185 13455
(.branch 1184 13239
(.branch 1183 37757
.empty
.empty)
.empty)
(.branch 1186 13408
.empty
.empty))
(.branch 1189 37654
(.branch 1188 37806
.empty
.empty)
(.branch 1190 37721
.empty
.empty)))
(.branch 1196 13293
(.branch 1194 13385
(.branch 1193 37708
(.branch 1192 13341
.empty
.empty)
.empty)
(.branch 1195 37784
.empty
.empty))
(.branch 1198 13369
(.branch 1197 37692
.empty
.empty)
(.branch 1199 37736
.empty
.empty))))
(.branch 1209 13342
(.branch 1205 37667
(.branch 1203 37831
(.branch 1202 13430
(.branch 1201 37619
.empty
.empty)
.empty)
(.branch 1204 13266
.empty
.empty))
(.branch 1207 37847
(.branch 1206 13478
.empty
.empty)
(.branch 1208 37711
.empty
.empty)))
(.branch 1214 37739
(.branch 1212 37695
(.branch 1211 13386
(.branch 1210 37787
.empty
.empty)
.empty)
(.branch 1213 13294
.empty
.empty))
(.branch 1216 37616
(.branch 1215 13370
.empty
.empty)
(.branch 1217 13249
.empty
.empty))))))
(.branch 1254 37660
(.branch 1236 13466
(.branch 1227 37712
(.branch 1223 13477
(.branch 1221 13265
(.branch 1220 37664
(.branch 1219 13429
.empty
.empty)
.empty)
(.branch 1222 37844
.empty
.empty))
(.branch 1225 37796
(.branch 1224 13397
.empty
.empty)
(.branch 1226 13345
.empty
.empty)))
(.branch 1232 13418
(.branch 1230 13297
(.branch 1229 37748
(.branch 1228 13381
.empty
.empty)
.empty)
(.branch 1231 37696
.empty
.empty))
(.branch 1234 13246
(.branch 1233 37819
.empty
.empty)
(.branch 1235 37615
.empty
.empty))))
(.branch 1245 13382
(.branch 1241 13398
(.branch 1239 37663
(.branch 1238 13262
(.branch 1237 37835
.empty
.empty)
.empty)
(.branch 1240 37799
.empty
.empty))
(.branch 1243 13346
(.branch 1242 37715
.empty
.empty)
(.branch 1244 37751
.empty
.empty)))
(.branch 1250 37612
(.branch 1248 37816
(.branch 1247 13298
(.branch 1246 37699
.empty
.empty)
.empty)
(.branch 1249 13417
.empty
.empty))
(.branch 1252 37832
(.branch 1251 13245
.empty
.empty)
(.branch 1253 13465
.empty
.empty)))))
(.branch 1272 16459
(.branch 1263 40917
(.branch 1259 40821
(.branch 1257 40858
(.branch 1256 16539
(.branch 1255 13261
.empty
.empty)
.empty)
(.branch 1258 16500
.empty
.empty))
(.branch 1261 40890
(.branch 1260 16443
.empty
.empty)
(.branch 1262 16468
.empty
.empty)))
(.branch 1268 16319
(.branch 1266 16368
(.branch 1265 40734
(.branch 1264 16415
.empty
.empty)
.empty)
(.branch 1267 40689
.empty
.empty))
(.branch 1270 16336
(.branch 1269 40766
.empty
.empty)
(.branch 1271 40785
.empty
.empty))))
(.branch 1281 40782
(.branch 1277 40810
(.branch 1275 40901
(.branch 1274 16452
(.branch 1273 40906
.empty
.empty)
.empty)
(.branch 1276 16491
.empty
.empty))
(.branch 1279 40869
(.branch 1278 16548
.empty
.empty)
(.branch 1280 16335
.empty
.empty)))
(.branch 1286 16416
(.branch 1284 16367
(.branch 1283 40769
(.branch 1282 16320
.empty
.empty)
.empty)
(.branch 1285 40686
.empty
.empty))
(.branch 1288 16419
(.branch 1287 40737
.empty
.empty)
(.branch 1289 40738
.empty
.empty)))))))
(.branch 1362 40844
(.branch 1326 40696
(.branch 1308 16371
(.branch 1299 40809
(.branch 1295 40781
(.branch 1293 40770
(.branch 1292 16323
(.branch 1291 40685
.empty
.empty)
.empty)
(.branch 1294 16332
.empty
.empty))
(.branch 1297 40870
(.branch 1296 16551
.empty
.empty)
(.branch 1298 16488
.empty
.empty)))
(.branch 1304 16339
(.branch 1302 16456
(.branch 1301 40902
(.branch 1300 16455
.empty
.empty)
.empty)
(.branch 1303 40905
.empty
.empty))
(.branch 1306 16316
(.branch 1305 40786
.empty
.empty)
(.branch 1307 40765
.empty
.empty))))
(.branch 1317 40822
(.branch 1313 40918
(.branch 1311 40733
(.branch 1310 16412
(.branch 1309 40690
.empty
.empty)
.empty)
(.branch 1312 16471
.empty
.empty))
(.branch 1315 40889
(.branch 1314 16440
.empty
.empty)
(.branch 1316 16503
.empty
.empty)))
(.branch 1322 16513
(.branch 1320 16509
(.branch 1319 40857
(.branch 1318 16536
.empty
.empty)
.empty)
(.branch 1321 16357
.empty
.empty))
(.branch 1324 40708
(.branch 1323 16345
.empty
.empty)
(.branch 1325 40924
.empty
.empty)))))
(.branch 1344 16530
(.branch 1335 40759
(.branch 1331 16430
(.branch 1329 16434
(.branch 1328 16394
(.branch 1327 40928
.empty
.empty)
.empty)
(.branch 1330 16406
.empty
.empty))
(.branch 1333 40747
(.branch 1332 40851
.empty
.empty)
(.branch 1334 40847
.empty
.empty)))
(.branch 1340 40828
(.branch 1338 16377
(.branch 1337 16477
(.branch 1336 16389
.empty
.empty)
.empty)
(.branch 1339 16481
.empty
.empty))
(.branch 1342 40832
(.branch 1341 40804
.empty
.empty)
(.branch 1343 40792
.empty
.empty))))
(.branch 1353 40927
(.branch 1349 40883
(.branch 1347 16310
(.branch 1346 16526
(.branch 1345 16298
.empty
.empty)
.empty)
(.branch 1348 40715
.empty
.empty))
(.branch 1351 40879
(.branch 1350 40727
.empty
.empty)
(.branch 1352 40711
.empty
.empty)))
(.branch 1358 16514
(.branch 1356 16510
(.branch 1355 40931
(.branch 1354 40699
.empty
.empty)
.empty)
(.branch 1357 16358
.empty
.empty))
(.branch 1360 40848
(.branch 1359 16346
.empty
.empty)
(.branch 1361 40744
.empty
.empty))))))
(.branch 1398 33009
(.branch 1380 16529
(.branch 1371 40795
(.branch 1367 16429
(.branch 1365 16433
(.branch 1364 16393
(.branch 1363 40756
.empty
.empty)
.empty)
(.branch 1366 16405
.empty
.empty))
(.branch 1369 40807
(.branch 1368 40831
.empty
.empty)
(.branch 1370 40835
.empty
.empty)))
(.branch 1376 40712
(.branch 1374 16378
(.branch 1373 16478
(.branch 1372 16390
.empty
.empty)
.empty)
(.branch 1375 16482
.empty
.empty))
(.branch 1378 40724
(.branch 1377 40880
.empty
.empty)
(.branch 1379 40876
.empty
.empty))))
(.branch 1389 289
(.branch 1385 33058
(.branch 1383 16309
(.branch 1382 16525
(.branch 1381 16297
.empty
.empty)
.empty)
(.branch 1384 35
.empty
.empty))
(.branch 1387 33021
(.branch 1386 310
.empty
.empty)
(.branch 1388 33054
.empty
.empty)))
(.branch 1394 312
(.branch 1392 309
(.branch 1391 12
(.branch 1390 33025
.empty
.empty)
.empty)
(.branch 1393 33037
.empty
.empty))
(.branch 1396 33041
(.branch 1395 33005
.empty
.empty)
(.branch 1397 11
.empty
.empty)))))
(.branch 1416 33063
(.branch 1407 287
(.branch 1403 33042
(.branch 1401 33010
(.branch 1400 36
(.branch 1399 14
.empty
.empty)
.empty)
(.branch 1402 33
.empty
.empty))
(.branch 1405 290
(.branch 1404 33006
.empty
.empty)
(.branch 1406 33038
.empty
.empty)))
(.branch 1412 33022
(.branch 1410 311
(.branch 1409 33026
(.branch 1408 34
.empty
.empty)
.empty)
(.branch 1411 33053
.empty
.empty))
(.branch 1414 33057
(.branch 1413 288
.empty
.empty)
(.branch 1415 13
.empty
.empty))))
(.branch 1425 350
(.branch 1421 33060
(.branch 1419 351
(.branch 1418 33016
(.branch 1417 76
.empty
.empty)
.empty)
(.branch 1420 56
.empty
.empty))
(.branch 1423 33019
(.branch 1422 331
.empty
.empty)
(.branch 1424 33032
.empty
.empty)))
(.branch 1429 33035
(.branch 1427 353
(.branch 1426 33000
.empty
.empty)
(.branch 1428 330
.empty
.empty))
(.branch 1431 33003
(.branch 1430 333
.empty
.empty)
(.branch 1432 33015
.empty
.empty))))))))
(.branch 1576 34554
(.branch 1505 367
(.branch 1469 1166
(.branch 1451 1143
(.branch 1442 33048
(.branch 1438 54
(.branch 1436 57
(.branch 1435 74
(.branch 1434 33047
.empty
.empty)
.empty)
(.branch 1437 33012
.empty
.empty))
(.branch 1440 33031
(.branch 1439 33044
.empty
.empty)
(.branch 1441 75
.empty
.empty)))
(.branch 1447 33051
(.branch 1445 33028
(.branch 1444 55
(.branch 1443 352
.empty
.empty)
.empty)
(.branch 1446 332
.empty
.empty))
(.branch 1449 1137
(.branch 1448 140
.empty
.empty)
(.branch 1450 89
.empty
.empty))))
(.branch 1460 1179
(.branch 1456 383
(.branch 1454 1176
(.branch 1453 141
(.branch 1452 1182
.empty
.empty)
.empty)
(.branch 1455 90
.empty
.empty))
(.branch 1458 124
(.branch 1457 1140
.empty
.empty)
(.branch 1459 1133
.empty
.empty)))
(.branch 1465 142
(.branch 1463 125
(.branch 1462 1186
(.branch 1461 384
.empty
.empty)
.empty)
(.branch 1464 1150
.empty
.empty))
(.branch 1467 91
(.branch 1466 1144
.empty
.empty)
(.branch 1468 419
.empty
.empty)))))
(.branch 1487 108
(.branch 1478 403
(.branch 1474 1154
(.branch 1472 1147
(.branch 1471 1160
(.branch 1470 368
.empty
.empty)
.empty)
(.branch 1473 385
.empty
.empty))
(.branch 1476 110
(.branch 1475 126
.empty
.empty)
(.branch 1477 1163
.empty
.empty)))
(.branch 1483 1131
(.branch 1481 1138
(.branch 1480 400
(.branch 1479 1170
.empty
.empty)
.empty)
(.branch 1482 107
.empty
.empty))
(.branch 1485 401
(.branch 1484 1181
.empty
.empty)
(.branch 1486 1188
.empty
.empty))))
(.branch 1496 1149
(.branch 1492 1191
(.branch 1490 416
(.branch 1489 1128
(.branch 1488 365
.empty
.empty)
.empty)
(.branch 1491 1134
.empty
.empty))
(.branch 1494 1185
(.branch 1493 366
.empty
.empty)
(.branch 1495 417
.empty
.empty)))
(.branch 1501 1165
(.branch 1499 109
(.branch 1498 1156
(.branch 1497 402
.empty
.empty)
.empty)
(.branch 1500 127
.empty
.empty))
(.branch 1503 1172
(.branch 1502 386
.empty
.empty)
(.branch 1504 1159
.empty
.empty))))))
(.branch 1541 34724
(.branch 1523 10173
(.branch 1514 34756
(.branch 1510 143
(.branch 1508 92
(.branch 1507 418
(.branch 1506 1153
.empty
.empty)
.empty)
(.branch 1509 1175
.empty
.empty))
(.branch 1512 34544
(.branch 1511 1169
.empty
.empty)
(.branch 1513 10177
.empty
.empty)))
(.branch 1519 34759
(.branch 1517 34547
(.branch 1516 10178
(.branch 1515 10357
.empty
.empty)
.empty)
(.branch 1518 10358
.empty
.empty))
(.branch 1521 10345
(.branch 1520 34744
.empty
.empty)
(.branch 1522 34540
.empty
.empty))))
(.branch 1532 10269
(.branch 1528 34639
(.branch 1526 10174
(.branch 1525 34747
(.branch 1524 10346
.empty
.empty)
.empty)
(.branch 1527 34543
.empty
.empty))
(.branch 1530 34715
(.branch 1529 10270
.empty
.empty)
(.branch 1531 10314
.empty
.empty)))
(.branch 1537 10326
(.branch 1535 34712
(.branch 1534 10313
(.branch 1533 34636
.empty
.empty)
.empty)
(.branch 1536 34727
.empty
.empty))
(.branch 1539 10274
(.branch 1538 34643
.empty
.empty)
(.branch 1540 10325
.empty
.empty)))))
(.branch 1559 34591
(.branch 1550 10406
(.branch 1546 34772
(.branch 1544 34592
(.branch 1543 34640
(.branch 1542 10273
.empty
.empty)
.empty)
(.branch 1545 10193
.empty
.empty))
(.branch 1548 10194
(.branch 1547 10405
.empty
.empty)
(.branch 1549 34595
.empty
.empty)))
(.branch 1555 10189
(.branch 1553 10393
(.branch 1552 34760
(.branch 1551 34775
.empty
.empty)
.empty)
(.branch 1554 34588
.empty
.empty))
(.branch 1557 34763
(.branch 1556 10394
.empty
.empty)
(.branch 1558 10190
.empty
.empty))))
(.branch 1568 34679
(.branch 1564 10221
(.branch 1562 34667
(.branch 1561 10222
(.branch 1560 34623
.empty
.empty)
.empty)
(.branch 1563 10298
.empty
.empty))
(.branch 1566 10297
(.branch 1565 34620
.empty
.empty)
(.branch 1567 34664
.empty
.empty)))
(.branch 1572 10309
(.branch 1570 34627
(.branch 1569 10310
.empty
.empty)
(.branch 1571 10226
.empty
.empty))
(.branch 1574 10225
(.branch 1573 34676
.empty
.empty)
(.branch 1575 34624
.empty
.empty)))))))
(.branch 1648 302
(.branch 1612 34734
(.branch 1594 10260
(.branch 1585 34650
(.branch 1581 34570
(.branch 1579 34613
(.branch 1578 34701
(.branch 1577 34786
.empty
.empty)
.empty)
(.branch 1580 34738
.empty
.empty))
(.branch 1583 34685
(.branch 1582 34661
.empty
.empty)
(.branch 1584 34690
.empty
.empty)))
(.branch 1590 34781
(.branch 1588 34602
(.branch 1587 34733
(.branch 1586 34581
.empty
.empty)
.empty)
(.branch 1589 34706
.empty
.empty))
(.branch 1592 10371
(.branch 1591 34565
.empty
.empty)
(.branch 1593 10203
.empty
.empty))))
(.branch 1603 10164
(.branch 1599 10244
(.branch 1597 10387
(.branch 1596 10155
(.branch 1595 10284
.empty
.empty)
.empty)
(.branch 1598 10332
.empty
.empty))
(.branch 1601 10339
(.branch 1600 10235
.empty
.empty)
(.branch 1602 10380
.empty
.empty)))
(.branch 1608 34566
(.branch 1606 10212
(.branch 1605 10251
(.branch 1604 10291
.empty
.empty)
.empty)
(.branch 1607 10364
.empty
.empty))
(.branch 1610 34705
(.branch 1609 34782
.empty
.empty)
(.branch 1611 34601
.empty
.empty)))))
(.branch 1630 10336
(.branch 1621 34702
(.branch 1617 34662
(.branch 1615 34689
(.branch 1614 34649
(.branch 1613 34582
.empty
.empty)
.empty)
(.branch 1616 34686
.empty
.empty))
(.branch 1619 34737
(.branch 1618 34569
.empty
.empty)
(.branch 1620 34614
.empty
.empty)))
(.branch 1626 10248
(.branch 1624 10367
(.branch 1623 34553
(.branch 1622 34785
.empty
.empty)
.empty)
(.branch 1625 10215
.empty
.empty))
(.branch 1628 10167
(.branch 1627 10288
.empty
.empty)
(.branch 1629 10383
.empty
.empty))))
(.branch 1639 10368
(.branch 1635 10152
(.branch 1633 10335
(.branch 1632 10247
(.branch 1631 10232
.empty
.empty)
.empty)
(.branch 1634 10384
.empty
.empty))
(.branch 1637 10263
(.branch 1636 10287
.empty
.empty)
(.branch 1638 10200
.empty
.empty)))
(.branch 1644 33230
(.branch 1642 25
(.branch 1641 33234
(.branch 1640 28
.empty
.empty)
.empty)
(.branch 1643 33202
.empty
.empty))
(.branch 1646 33198
(.branch 1645 282
.empty
.empty)
(.branch 1647 279
.empty
.empty))))))
(.branch 1684 33201
(.branch 1666 33208
(.branch 1657 69
(.branch 1653 4
(.branch 1651 33213
(.branch 1650 27
(.branch 1649 33250
.empty
.empty)
.empty)
(.branch 1652 33246
.empty
.empty))
(.branch 1655 281
(.branch 1654 33217
.empty
.empty)
(.branch 1656 33239
.empty
.empty)))
(.branch 1662 46
(.branch 1660 49
(.branch 1659 66
(.branch 1658 33207
.empty
.empty)
.empty)
(.branch 1661 33236
.empty
.empty))
(.branch 1664 33255
(.branch 1663 33204
.empty
.empty)
(.branch 1665 343
.empty
.empty))))
(.branch 1675 33245
(.branch 1671 33211
(.branch 1669 33252
(.branch 1668 323
(.branch 1667 68
.empty
.empty)
.empty)
(.branch 1670 48
.empty
.empty))
(.branch 1673 33218
(.branch 1672 303
.empty
.empty)
(.branch 1674 26
.empty
.empty)))
(.branch 1680 301
(.branch 1678 33249
(.branch 1677 5
(.branch 1676 33214
.empty
.empty)
.empty)
(.branch 1679 280
.empty
.empty))
(.branch 1682 304
(.branch 1681 33197
.empty
.empty)
(.branch 1683 33229
.empty
.empty)))))
(.branch 1702 325
(.branch 1693 33220
(.branch 1689 344
(.branch 1687 6
(.branch 1686 33233
(.branch 1685 3
.empty
.empty)
.empty)
(.branch 1688 33223
.empty
.empty))
(.branch 1691 67
(.branch 1690 33240
.empty
.empty)
(.branch 1692 324
.empty
.empty)))
(.branch 1698 33224
(.branch 1696 33192
(.branch 1695 33243
(.branch 1694 47
.empty
.empty)
.empty)
(.branch 1697 342
.empty
.empty))
(.branch 1700 322
(.branch 1699 345
.empty
.empty)
(.branch 1701 33195
.empty
.empty))))
(.branch 1711 573
(.branch 1707 568
(.branch 1705 200
(.branch 1704 161
(.branch 1703 33227
.empty
.empty)
.empty)
(.branch 1706 574
.empty
.empty))
(.branch 1709 175
(.branch 1708 464
.empty
.empty)
(.branch 1710 580
.empty
.empty)))
(.branch 1715 477
(.branch 1713 584
(.branch 1712 590
.empty
.empty)
(.branch 1714 438
.empty
.empty))
(.branch 1717 589
(.branch 1716 596
.empty
.empty)
(.branch 1718 189
.empty
.empty)))))))))
(.branch 2006 37808
(.branch 1863 40877
(.branch 1791 40919
(.branch 1755 186
(.branch 1737 188
(.branch 1728 160
(.branch 1724 555
(.branch 1722 159
(.branch 1721 567
(.branch 1720 561
.empty
.empty)
.empty)
(.branch 1723 198
.empty
.empty))
(.branch 1726 462
(.branch 1725 562
.empty
.empty)
(.branch 1727 173
.empty
.empty)))
(.branch 1733 174
(.branch 1731 600
(.branch 1730 606
(.branch 1729 199
.empty
.empty)
.empty)
(.branch 1732 463
.empty
.empty))
(.branch 1735 605
(.branch 1734 612
.empty
.empty)
(.branch 1736 451
.empty
.empty))))
(.branch 1746 176
(.branch 1742 583
(.branch 1740 476
(.branch 1739 571
(.branch 1738 578
.empty
.empty)
.empty)
(.branch 1741 437
.empty
.empty))
(.branch 1744 594
(.branch 1743 577
.empty
.empty)
(.branch 1745 587
.empty
.empty)))
(.branch 1751 162
(.branch 1749 593
(.branch 1748 599
(.branch 1747 465
.empty
.empty)
.empty)
(.branch 1750 201
.empty
.empty))
(.branch 1753 564
(.branch 1752 557
.empty
.empty)
(.branch 1754 449
.empty
.empty)))))
(.branch 1773 16470
(.branch 1764 475
(.branch 1760 450
(.branch 1758 474
(.branch 1757 558
(.branch 1756 552
.empty
.empty)
.empty)
(.branch 1759 435
.empty
.empty))
(.branch 1762 610
(.branch 1761 187
.empty
.empty)
(.branch 1763 603
.empty
.empty)))
(.branch 1769 40891
(.branch 1767 609
(.branch 1766 615
(.branch 1765 436
.empty
.empty)
.empty)
(.branch 1768 16537
.empty
.empty))
(.branch 1771 40888
(.branch 1770 16538
.empty
.empty)
(.branch 1772 40820
.empty
.empty))))
(.branch 1782 16369
(.branch 1778 40732
(.branch 1776 40735
(.branch 1775 16469
(.branch 1774 40823
.empty
.empty)
.empty)
(.branch 1777 16317
.empty
.empty))
(.branch 1780 16370
(.branch 1779 16318
.empty
.empty)
(.branch 1781 40784
.empty
.empty)))
(.branch 1787 16442
(.branch 1785 16441
(.branch 1784 40859
(.branch 1783 40787
.empty
.empty)
.empty)
(.branch 1786 40856
.empty
.empty))
(.branch 1789 40916
(.branch 1788 16502
.empty
.empty)
(.branch 1790 16501
.empty
.empty))))))
(.branch 1827 16366
(.branch 1809 40687
(.branch 1800 40907
(.branch 1796 40688
(.branch 1794 16414
(.branch 1793 40767
(.branch 1792 16413
.empty
.empty)
.empty)
(.branch 1795 40764
.empty
.empty))
(.branch 1798 40691
(.branch 1797 16338
.empty
.empty)
(.branch 1799 16337
.empty
.empty)))
(.branch 1805 40868
(.branch 1803 16490
(.branch 1802 40904
(.branch 1801 16489
.empty
.empty)
.empty)
(.branch 1804 16454
.empty
.empty))
(.branch 1807 40871
(.branch 1806 16453
.empty
.empty)
(.branch 1808 16333
.empty
.empty))))
(.branch 1818 16458
(.branch 1814 40771
(.branch 1812 40768
(.branch 1811 40684
(.branch 1810 16334
.empty
.empty)
.empty)
(.branch 1813 16418
.empty
.empty))
(.branch 1816 16457
(.branch 1815 16417
.empty
.empty)
(.branch 1817 40811
.empty
.empty)))
(.branch 1823 16549
(.branch 1821 16550
(.branch 1820 40900
(.branch 1819 40808
.empty
.empty)
.empty)
(.branch 1822 40903
.empty
.empty))
(.branch 1825 16365
(.branch 1824 40783
.empty
.empty)
(.branch 1826 40780
.empty
.empty)))))
(.branch 1845 40725
(.branch 1836 16379
(.branch 1832 16511
(.branch 1830 16321
(.branch 1829 40736
(.branch 1828 16322
.empty
.empty)
.empty)
(.branch 1831 40739
.empty
.empty))
(.branch 1834 16479
(.branch 1833 40830
.empty
.empty)
(.branch 1835 40926
.empty
.empty)))
(.branch 1841 40849
(.branch 1839 40794
(.branch 1838 16347
(.branch 1837 40698
.empty
.empty)
.empty)
(.branch 1840 16528
.empty
.empty))
(.branch 1843 40881
(.branch 1842 16432
.empty
.empty)
(.branch 1844 16404
.empty
.empty))))
(.branch 1854 16483
(.branch 1850 16359
(.branch 1848 16391
(.branch 1847 40757
(.branch 1846 16308
.empty
.empty)
.empty)
(.branch 1849 40710
.empty
.empty))
(.branch 1852 16515
(.branch 1851 40806
.empty
.empty)
(.branch 1853 40834
.empty
.empty)))
(.branch 1859 40745
(.branch 1857 40713
(.branch 1856 16392
(.branch 1855 40930
.empty
.empty)
.empty)
(.branch 1858 16296
.empty
.empty))
(.branch 1861 40845
(.branch 1860 16524
.empty
.empty)
(.branch 1862 16428
.empty
.empty)))))))
(.branch 1935 13260
(.branch 1899 13428
(.branch 1881 40758
(.branch 1872 16480
(.branch 1868 16299
(.branch 1866 16527
(.branch 1865 40878
(.branch 1864 16431
.empty
.empty)
.empty)
(.branch 1867 40846
.empty
.empty))
(.branch 1870 16395
(.branch 1869 40746
.empty
.empty)
(.branch 1871 40714
.empty
.empty)))
(.branch 1877 40805
(.branch 1875 40833
(.branch 1874 16512
(.branch 1873 40929
.empty
.empty)
.empty)
(.branch 1876 16356
.empty
.empty))
(.branch 1879 40709
(.branch 1878 16388
.empty
.empty)
(.branch 1880 16311
.empty
.empty))))
(.branch 1890 16376
(.branch 1886 16531
(.branch 1884 16435
(.branch 1883 40726
(.branch 1882 16407
.empty
.empty)
.empty)
(.branch 1885 40882
.empty
.empty))
(.branch 1888 16344
(.branch 1887 40850
.empty
.empty)
(.branch 1889 40793
.empty
.empty)))
(.branch 1895 40829
(.branch 1893 40925
(.branch 1892 16476
(.branch 1891 40697
.empty
.empty)
.empty)
(.branch 1894 16508
.empty
.empty))
(.branch 1897 13387
(.branch 1896 13343
.empty
.empty)
(.branch 1898 13248
.empty
.empty)))))
(.branch 1917 13419
(.branch 1908 37694
(.branch 1904 37710
(.branch 1902 13264
(.branch 1901 13371
(.branch 1900 13295
.empty
.empty)
.empty)
(.branch 1903 13476
.empty
.empty))
(.branch 1906 37617
(.branch 1905 37786
.empty
.empty)
(.branch 1907 37829
.empty
.empty)))
(.branch 1913 13467
(.branch 1911 37845
(.branch 1910 37665
(.branch 1909 37738
.empty
.empty)
.empty)
(.branch 1912 13263
.empty
.empty))
(.branch 1915 13380
(.branch 1914 13296
.empty
.empty)
(.branch 1916 13247
.empty
.empty))))
(.branch 1926 37713
(.branch 1922 37697
(.branch 1920 37662
(.branch 1919 13396
(.branch 1918 13344
.empty
.empty)
.empty)
(.branch 1921 37834
.empty
.empty))
(.branch 1924 37614
(.branch 1923 37749
.empty
.empty)
(.branch 1925 37818
.empty
.empty)))
(.branch 1931 13244
(.branch 1929 13347
(.branch 1928 13399
(.branch 1927 37797
.empty
.empty)
.empty)
(.branch 1930 13416
.empty
.empty))
(.branch 1933 13299
(.branch 1932 13383
.empty
.empty)
(.branch 1934 13464
.empty
.empty))))))
(.branch 1971 37732
(.branch 1953 37666
(.branch 1944 13479
(.branch 1940 37750
(.branch 1938 37817
(.branch 1937 37714
(.branch 1936 37798
.empty
.empty)
.empty)
(.branch 1939 37613
.empty
.empty))
(.branch 1942 37833
(.branch 1941 37698
.empty
.empty)
(.branch 1943 37661
.empty
.empty)))
(.branch 1949 13251
(.branch 1947 13292
(.branch 1946 13368
(.branch 1945 13267
.empty
.empty)
.empty)
(.branch 1948 13431
.empty
.empty))
(.branch 1951 13340
(.branch 1950 13384
.empty
.empty)
(.branch 1952 37846
.empty
.empty))))
(.branch 1962 13409
(.branch 1958 37785
(.branch 1956 37830
(.branch 1955 37693
(.branch 1954 37737
.empty
.empty)
.empty)
(.branch 1957 37618
.empty
.empty))
(.branch 1960 13305
(.branch 1959 37709
.empty
.empty)
(.branch 1961 37760
.empty
.empty)))
(.branch 1967 37807
(.branch 1965 37655
(.branch 1964 13454
(.branch 1963 37720
.empty
.empty)
.empty)
(.branch 1966 13238
.empty
.empty))
(.branch 1969 37756
(.branch 1968 13317
.empty
.empty)
(.branch 1970 13405
.empty
.empty)))))
(.branch 1989 37859
(.branch 1980 13286
(.branch 1976 13361
(.branch 1974 13226
(.branch 1973 37643
(.branch 1972 13458
.empty
.empty)
.empty)
(.branch 1975 37811
.empty
.empty))
(.branch 1978 13321
(.branch 1977 37672
.empty
.empty)
(.branch 1979 37776
.empty
.empty)))
(.branch 1985 37684
(.branch 1983 37639
(.branch 1982 13438
(.branch 1981 37855
.empty
.empty)
.empty)
(.branch 1984 13357
.empty
.empty))
(.branch 1987 37772
(.branch 1986 13333
.empty
.empty)
(.branch 1988 13274
.empty
.empty))))
(.branch 1998 37804
(.branch 1994 37723
(.branch 1992 37763
(.branch 1991 37627
(.branch 1990 13442
.empty
.empty)
.empty)
(.branch 1993 13306
.empty
.empty))
(.branch 1996 37652
(.branch 1995 13410
.empty
.empty)
(.branch 1997 13453
.empty
.empty)))
(.branch 2002 37735
(.branch 2000 37759
(.branch 1999 13237
.empty
.empty)
(.branch 2001 13318
.empty
.empty))
(.branch 2004 37640
(.branch 2003 13406
.empty
.empty)
(.branch 2005 13457
.empty
.empty))))))))
(.branch 2149 40921
(.branch 2078 40864
(.branch 2042 16450
(.branch 2024 16541
(.branch 2015 13437
(.branch 2011 13322
(.branch 2009 13362
(.branch 2008 37675
(.branch 2007 13225
.empty
.empty)
.empty)
(.branch 2010 37779
.empty
.empty))
(.branch 2013 13285
(.branch 2012 37852
.empty
.empty)
(.branch 2014 37636
.empty
.empty)))
(.branch 2020 37856
(.branch 2018 37775
(.branch 2017 13358
(.branch 2016 37687
.empty
.empty)
.empty)
(.branch 2019 13334
.empty
.empty))
(.branch 2022 37624
(.branch 2021 13273
.empty
.empty)
(.branch 2023 13441
.empty
.empty))))
(.branch 2033 40728
(.branch 2029 16313
(.branch 2027 16374
(.branch 2026 16362
(.branch 2025 16545
.empty
.empty)
.empty)
(.branch 2028 16325
.empty
.empty))
(.branch 2031 16462
(.branch 2030 16466
.empty
.empty)
(.branch 2032 40740
.empty
.empty)))
(.branch 2038 40779
(.branch 2036 40892
(.branch 2035 40815
(.branch 2034 40819
.empty
.empty)
.empty)
(.branch 2037 40896
.empty
.empty))
(.branch 2040 16341
(.branch 2039 40791
.empty
.empty)
(.branch 2041 16329
.empty
.empty)))))
(.branch 2060 40895
(.branch 2051 40775
(.branch 2047 16422
(.branch 2045 16497
(.branch 2044 16493
(.branch 2043 16446
.empty
.empty)
.empty)
(.branch 2046 16410
.empty
.empty))
(.branch 2049 40912
(.branch 2048 40908
.empty
.empty)
(.branch 2050 40763
.empty
.empty)))
(.branch 2056 40743
(.branch 2054 40867
(.branch 2053 40680
(.branch 2052 40692
.empty
.empty)
.empty)
(.branch 2055 40863
.empty
.empty))
(.branch 2058 40816
(.branch 2057 40731
.empty
.empty)
(.branch 2059 40812
.empty
.empty))))
(.branch 2069 16314
(.branch 2065 16546
(.branch 2063 40788
(.branch 2062 40776
(.branch 2061 40899
.empty
.empty)
.empty)
(.branch 2064 16542
.empty
.empty))
(.branch 2067 16373
(.branch 2066 16361
.empty
.empty)
(.branch 2068 16326
.empty
.empty)))
(.branch 2074 40760
(.branch 2072 40911
(.branch 2071 16461
(.branch 2070 16465
.empty
.empty)
.empty)
(.branch 2073 40915
.empty
.empty))
(.branch 2076 40695
(.branch 2075 40772
.empty
.empty)
(.branch 2077 40683
.empty
.empty))))))
(.branch 2114 16399
(.branch 2096 16303
(.branch 2087 16421
(.branch 2083 16445
(.branch 2081 16330
(.branch 2080 16342
(.branch 2079 40860
.empty
.empty)
.empty)
(.branch 2082 16449
.empty
.empty))
(.branch 2085 16498
(.branch 2084 16494
.empty
.empty)
(.branch 2086 16409
.empty
.empty)))
(.branch 2092 16484
(.branch 2090 16523
(.branch 2089 40874
(.branch 2088 16507
.empty
.empty)
.empty)
(.branch 2091 40922
.empty
.empty))
(.branch 2094 16436
(.branch 2093 40853
.empty
.empty)
(.branch 2095 40837
.empty
.empty))))
(.branch 2105 40826
(.branch 2101 40801
(.branch 2099 40718
(.branch 2098 16351
(.branch 2097 40702
.empty
.empty)
.empty)
(.branch 2100 16400
.empty
.empty))
(.branch 2103 40753
(.branch 2102 16384
.empty
.empty)
(.branch 2104 16427
.empty
.empty)))
(.branch 2110 16516
(.branch 2108 16532
(.branch 2107 40842
(.branch 2106 16475
.empty
.empty)
.empty)
(.branch 2109 40933
.empty
.empty))
(.branch 2112 16383
(.branch 2111 40885
.empty
.empty)
(.branch 2113 40750
.empty
.empty)))))
(.branch 2132 16472
(.branch 2123 40722
(.branch 2119 40705
(.branch 2117 40721
(.branch 2116 16352
(.branch 2115 40798
.empty
.empty)
.empty)
(.branch 2118 16304
.empty
.empty))
(.branch 2121 40706
(.branch 2120 16307
.empty
.empty)
(.branch 2122 16355
.empty
.empty)))
(.branch 2128 16519
(.branch 2126 16380
(.branch 2125 40797
(.branch 2124 16396
.empty
.empty)
.empty)
(.branch 2127 40749
.empty
.empty))
(.branch 2130 16535
(.branch 2129 40886
.empty
.empty)
(.branch 2131 40934
.empty
.empty))))
(.branch 2141 40717
(.branch 2137 40754
(.branch 2135 40825
(.branch 2134 16424
(.branch 2133 40841
.empty
.empty)
.empty)
(.branch 2136 16387
.empty
.empty))
(.branch 2139 40802
(.branch 2138 16403
.empty
.empty)
(.branch 2140 16348
.empty
.empty)))
(.branch 2145 40838
(.branch 2143 40701
(.branch 2142 16300
.empty
.empty)
(.branch 2144 16439
.empty
.empty))
(.branch 2147 40854
(.branch 2146 16487
.empty
.empty)
(.branch 2148 16520
.empty
.empty)))))))
(.branch 2221 10213
(.branch 2185 10395
(.branch 2167 34541
(.branch 2158 34545
(.branch 2154 34625
(.branch 2152 34590
(.branch 2151 40873
(.branch 2150 16504
.empty
.empty)
.empty)
(.branch 2153 34762
.empty
.empty))
(.branch 2156 34638
(.branch 2155 34677
.empty
.empty)
(.branch 2157 34714
.empty
.empty)))
(.branch 2163 34621
(.branch 2161 34594
(.branch 2160 34774
(.branch 2159 34757
.empty
.empty)
.empty)
(.branch 2162 34665
.empty
.empty))
(.branch 2165 34642
(.branch 2164 34726
.empty
.empty)
(.branch 2166 34745
.empty
.empty))))
(.branch 2176 34758
(.branch 2172 34622
(.branch 2170 34641
(.branch 2169 34746
(.branch 2168 34542
.empty
.empty)
.empty)
(.branch 2171 34725
.empty
.empty))
(.branch 2174 34593
(.branch 2173 34666
.empty
.empty)
(.branch 2175 34773
.empty
.empty)))
(.branch 2181 34626
(.branch 2179 34637
(.branch 2178 34713
(.branch 2177 34546
.empty
.empty)
.empty)
(.branch 2180 34678
.empty
.empty))
(.branch 2183 34589
(.branch 2182 34761
.empty
.empty)
(.branch 2184 10191
.empty
.empty)))))
(.branch 2203 10324
(.branch 2194 10296
(.branch 2190 10176
(.branch 2188 10271
(.branch 2187 10308
(.branch 2186 10224
.empty
.empty)
.empty)
(.branch 2189 10315
.empty
.empty))
(.branch 2192 10407
(.branch 2191 10356
.empty
.empty)
(.branch 2193 10195
.empty
.empty)))
(.branch 2199 10172
(.branch 2197 10275
(.branch 2196 10327
(.branch 2195 10220
.empty
.empty)
.empty)
(.branch 2198 10344
.empty
.empty))
(.branch 2201 10347
(.branch 2200 10175
.empty
.empty)
(.branch 2202 10272
.empty
.empty))))
(.branch 2212 10311
(.branch 2208 10359
(.branch 2206 10192
(.branch 2205 10299
(.branch 2204 10223
.empty
.empty)
.empty)
(.branch 2207 10404
.empty
.empty))
(.branch 2210 10312
(.branch 2209 10179
.empty
.empty)
(.branch 2211 10268
.empty
.empty)))
(.branch 2217 10381
(.branch 2215 10188
(.branch 2214 10392
(.branch 2213 10227
.empty
.empty)
.empty)
(.branch 2216 34580
.empty
.empty))
(.branch 2219 10165
(.branch 2218 34732
.empty
.empty)
(.branch 2220 34780
.empty
.empty))))))
(.branch 2257 34571
(.branch 2239 10250
(.branch 2230 10366
(.branch 2226 10166
(.branch 2224 10382
(.branch 2223 10365
(.branch 2222 34564
.empty
.empty)
.empty)
(.branch 2225 34583
.empty
.empty))
(.branch 2228 10214
(.branch 2227 34735
.empty
.empty)
(.branch 2229 34783
.empty
.empty)))
(.branch 2235 10338
(.branch 2233 10234
(.branch 2232 34691
(.branch 2231 34567
.empty
.empty)
.empty)
(.branch 2234 34651
.empty
.empty))
(.branch 2237 10290
(.branch 2236 34603
.empty
.empty)
(.branch 2238 34707
.empty
.empty))))
(.branch 2248 34568
(.branch 2244 10289
(.branch 2242 10337
(.branch 2241 34688
(.branch 2240 10233
.empty
.empty)
.empty)
(.branch 2243 34648
.empty
.empty))
(.branch 2246 10249
(.branch 2245 34600
.empty
.empty)
(.branch 2247 34704
.empty
.empty)))
(.branch 2253 10201
(.branch 2251 10153
(.branch 2250 34736
(.branch 2249 10385
.empty
.empty)
.empty)
(.branch 2252 34784
.empty
.empty))
(.branch 2255 10369
(.branch 2254 34552
.empty
.empty)
(.branch 2256 10386
.empty
.empty)))))
(.branch 2275 34660
(.branch 2266 34663
(.branch 2262 10370
(.branch 2260 10202
(.branch 2259 34739
(.branch 2258 10154
.empty
.empty)
.empty)
(.branch 2261 34787
.empty
.empty))
(.branch 2264 34687
(.branch 2263 34555
.empty
.empty)
(.branch 2265 10246
.empty
.empty)))
(.branch 2271 10262
(.branch 2269 10286
(.branch 2268 34615
(.branch 2267 10334
.empty
.empty)
.empty)
(.branch 2270 34703
.empty
.empty))
(.branch 2273 34684
(.branch 2272 10245
.empty
.empty)
(.branch 2274 10333
.empty
.empty))))
(.branch 2284 1105
(.branch 2280 422
(.branch 2278 10261
(.branch 2277 34612
(.branch 2276 10285
.empty
.empty)
.empty)
(.branch 2279 34700
.empty
.empty))
(.branch 2282 1089
(.branch 2281 371
.empty
.empty)
(.branch 2283 1095
.empty
.empty)))
(.branch 2288 113
(.branch 2286 147
(.branch 2285 1111
.empty
.empty)
(.branch 2287 96
.empty
.empty))
(.branch 2290 1092
(.branch 2289 406
.empty
.empty)
(.branch 2291 1085
.empty
.empty)))))))))))
(.branch 3438 92952
(.branch 2865 89040
(.branch 2579 92914
(.branch 2436 10216
(.branch 2364 32
(.branch 2328 1069
(.branch 2310 1124
(.branch 2301 370
(.branch 2297 1064
(.branch 2295 131
(.branch 2294 390
(.branch 2293 1101
.empty
.empty)
.empty)
(.branch 2296 1070
.empty
.empty))
(.branch 2299 369
(.branch 2298 420
.empty
.empty)
(.branch 2300 421
.empty
.empty)))
(.branch 2306 111
(.branch 2304 1067
(.branch 2303 1127
(.branch 2302 1121
.empty
.empty)
.empty)
(.branch 2305 1074
.empty
.empty))
(.branch 2308 112
(.branch 2307 404
.empty
.empty)
(.branch 2309 405
.empty
.empty))))
(.branch 2319 114
(.branch 2315 1083
(.branch 2313 389
(.branch 2312 130
(.branch 2311 1117
.empty
.empty)
.empty)
(.branch 2314 1090
.empty
.empty))
(.branch 2317 1099
(.branch 2316 1106
.empty
.empty)
(.branch 2318 407
.empty
.empty)))
(.branch 2324 1096
(.branch 2322 1080
(.branch 2321 146
(.branch 2320 95
.empty
.empty)
.empty)
(.branch 2323 1086
.empty
.empty))
(.branch 2326 372
(.branch 2325 1102
.empty
.empty)
(.branch 2327 423
.empty
.empty)))))
(.branch 2346 308
(.branch 2337 1073
(.branch 2333 388
(.branch 2331 387
(.branch 2330 128
(.branch 2329 1076
.empty
.empty)
.empty)
(.branch 2332 129
.empty
.empty))
(.branch 2335 1115
(.branch 2334 1122
.empty
.empty)
(.branch 2336 1079
.empty
.empty)))
(.branch 2342 1112
(.branch 2340 94
(.branch 2339 144
(.branch 2338 93
.empty
.empty)
.empty)
(.branch 2341 145
.empty
.empty))
(.branch 2344 305
(.branch 2343 1118
.empty
.empty)
(.branch 2345 32973
.empty
.empty))))
(.branch 2355 10
(.branch 2351 32957
(.branch 2349 32994
(.branch 2348 31
(.branch 2347 32941
.empty
.empty)
.empty)
(.branch 2350 306
.empty
.empty))
(.branch 2353 7
(.branch 2352 32977
.empty
.empty)
(.branch 2354 32945
.empty
.empty)))
(.branch 2360 30
(.branch 2358 32961
(.branch 2357 285
(.branch 2356 32990
.empty
.empty)
.empty)
(.branch 2359 8
.empty
.empty))
(.branch 2362 307
(.branch 2361 32962
.empty
.empty)
(.branch 2363 32989
.empty
.empty))))))
(.branch 2400 51
(.branch 2382 32952
(.branch 2373 286
(.branch 2369 284
(.branch 2367 32978
(.branch 2366 29
(.branch 2365 32946
.empty
.empty)
.empty)
(.branch 2368 32958
.empty
.empty))
(.branch 2371 9
(.branch 2370 32993
.empty
.empty)
(.branch 2372 32942
.empty
.empty)))
(.branch 2378 32936
(.branch 2376 32968
(.branch 2375 283
(.branch 2374 32974
.empty
.empty)
.empty)
(.branch 2377 346
.empty
.empty))
(.branch 2380 32999
(.branch 2379 349
.empty
.empty)
(.branch 2381 72
.empty
.empty))))
(.branch 2391 32955
(.branch 2387 32939
(.branch 2385 32971
(.branch 2384 326
(.branch 2383 347
.empty
.empty)
.empty)
(.branch 2386 329
.empty
.empty))
(.branch 2389 32996
(.branch 2388 52
.empty
.empty)
(.branch 2390 327
.empty
.empty)))
(.branch 2396 32951
(.branch 2394 32984
(.branch 2393 71
(.branch 2392 32967
.empty
.empty)
.empty)
(.branch 2395 348
.empty
.empty))
(.branch 2398 32983
(.branch 2397 73
.empty
.empty)
(.branch 2399 70
.empty
.empty)))))
(.branch 2418 34769
(.branch 2409 34586
(.branch 2405 32948
(.branch 2403 32987
(.branch 2402 328
(.branch 2401 32964
.empty
.empty)
.empty)
(.branch 2404 53
.empty
.empty))
(.branch 2407 32980
(.branch 2406 50
.empty
.empty)
(.branch 2408 34549
.empty
.empty)))
(.branch 2414 10196
(.branch 2412 10228
(.branch 2411 34618
(.branch 2410 34645
.empty
.empty)
.empty)
(.branch 2413 10267
.empty
.empty))
(.branch 2416 34673
(.branch 2415 10171
.empty
.empty)
(.branch 2417 34718
.empty
.empty))))
(.branch 2427 34754
(.branch 2423 10303
(.branch 2421 10399
(.branch 2420 10352
(.branch 2419 34750
.empty
.empty)
.empty)
(.branch 2422 10320
.empty
.empty))
(.branch 2425 34722
(.branch 2424 34669
.empty
.empty)
(.branch 2426 34765
.empty
.empty)))
(.branch 2432 34537
(.branch 2430 10316
(.branch 2429 10403
(.branch 2428 10348
.empty
.empty)
.empty)
(.branch 2431 10307
.empty
.empty))
(.branch 2434 34633
(.branch 2433 34598
.empty
.empty)
(.branch 2435 34630
.empty
.empty)))))))
(.branch 2508 10361
(.branch 2472 34559
(.branch 2454 10400
(.branch 2445 10187
(.branch 2441 34634
(.branch 2439 10183
(.branch 2438 10184
(.branch 2437 10279
.empty
.empty)
.empty)
(.branch 2440 34629
.empty
.empty))
(.branch 2443 34538
(.branch 2442 34597
.empty
.empty)
(.branch 2444 10180
.empty
.empty)))
(.branch 2450 34721
(.branch 2448 34753
(.branch 2447 10219
(.branch 2446 10276
.empty
.empty)
.empty)
(.branch 2449 34766
.empty
.empty))
(.branch 2452 10304
(.branch 2451 34670
.empty
.empty)
(.branch 2453 10319
.empty
.empty))))
(.branch 2463 10355
(.branch 2459 34674
(.branch 2457 34770
(.branch 2456 34749
(.branch 2455 10351
.empty
.empty)
.empty)
(.branch 2458 34717
.empty
.empty))
(.branch 2461 10323
(.branch 2460 10300
.empty
.empty)
(.branch 2462 10396
.empty
.empty)))
(.branch 2468 10168
(.branch 2466 34585
(.branch 2465 34646
(.branch 2464 34617
.empty
.empty)
.empty)
(.branch 2467 34550
.empty
.empty))
(.branch 2470 10264
(.branch 2469 10199
.empty
.empty)
(.branch 2471 10231
.empty
.empty)))))
(.branch 2490 34575
(.branch 2481 10257
(.branch 2477 10362
(.branch 2475 10206
(.branch 2474 34655
(.branch 2473 10238
.empty
.empty)
.empty)
(.branch 2476 34683
.empty
.empty))
(.branch 2479 10330
(.branch 2478 34779
.empty
.empty)
(.branch 2480 34576
.empty
.empty)))
(.branch 2486 34740
(.branch 2484 34708
(.branch 2483 10161
(.branch 2482 34608
.empty
.empty)
.empty)
(.branch 2485 10389
.empty
.empty))
(.branch 2488 34607
(.branch 2487 10293
.empty
.empty)
(.branch 2489 10158
.empty
.empty))))
(.branch 2499 10241
(.branch 2495 10378
(.branch 2493 10282
(.branch 2492 34731
(.branch 2491 10254
.empty
.empty)
.empty)
(.branch 2494 34699
.empty
.empty))
(.branch 2497 10209
(.branch 2496 34656
.empty
.empty)
(.branch 2498 34560
.empty
.empty)))
(.branch 2504 10237
(.branch 2502 34692
(.branch 2501 10341
(.branch 2500 34788
.empty
.empty)
.empty)
(.branch 2503 10373
.empty
.empty))
(.branch 2506 10205
(.branch 2505 34556
.empty
.empty)
(.branch 2507 34652
.empty
.empty))))))
(.branch 2544 93200
(.branch 2526 10377
(.branch 2517 34711
(.branch 2513 34579
(.branch 2511 34776
(.branch 2510 10329
(.branch 2509 34680
.empty
.empty)
.empty)
(.branch 2512 10258
.empty
.empty))
(.branch 2515 34611
(.branch 2514 10162
.empty
.empty)
(.branch 2516 10390
.empty
.empty)))
(.branch 2522 10253
(.branch 2520 10157
(.branch 2519 34743
(.branch 2518 10294
.empty
.empty)
.empty)
(.branch 2521 34604
.empty
.empty))
(.branch 2524 10281
(.branch 2523 34572
.empty
.empty)
(.branch 2525 34728
.empty
.empty))))
(.branch 2535 34695
(.branch 2531 34563
(.branch 2529 34659
(.branch 2528 10210
(.branch 2527 34696
.empty
.empty)
.empty)
(.branch 2530 10242
.empty
.empty))
(.branch 2533 34791
(.branch 2532 10342
.empty
.empty)
(.branch 2534 10374
.empty
.empty)))
(.branch 2540 92912
(.branch 2538 93130
(.branch 2537 93104
(.branch 2536 93080
.empty
.empty)
.empty)
(.branch 2539 93058
.empty
.empty))
(.branch 2542 93250
(.branch 2541 93272
.empty
.empty)
(.branch 2543 92938
.empty
.empty)))))
(.branch 2562 93201
(.branch 2553 93059
(.branch 2549 93008
(.branch 2547 93226
(.branch 2546 92962
(.branch 2545 92984
.empty
.empty)
.empty)
(.branch 2548 93176
.empty
.empty))
(.branch 2551 93154
(.branch 2550 93034
.empty
.empty)
(.branch 2552 93131
.empty
.empty)))
(.branch 2558 92913
(.branch 2556 93251
(.branch 2555 93105
(.branch 2554 93081
.empty
.empty)
.empty)
(.branch 2557 92939
.empty
.empty))
(.branch 2560 92963
(.branch 2559 93273
.empty
.empty)
(.branch 2561 93227
.empty
.empty))))
(.branch 2571 93178
(.branch 2567 93009
(.branch 2565 93155
(.branch 2564 93035
(.branch 2563 92985
.empty
.empty)
.empty)
(.branch 2566 93177
.empty
.empty))
(.branch 2569 93032
(.branch 2568 93152
.empty
.empty)
(.branch 2570 93010
.empty
.empty)))
(.branch 2575 93202
(.branch 2573 92960
(.branch 2572 93224
.empty
.empty)
(.branch 2574 92986
.empty
.empty))
(.branch 2577 93248
(.branch 2576 92936
.empty
.empty)
(.branch 2578 93274
.empty
.empty))))))))
(.branch 2722 79019
(.branch 2651 93033
(.branch 2615 93154
(.branch 2597 93083
(.branch 2588 92987
(.branch 2584 93011
(.branch 2582 93106
(.branch 2581 93128
(.branch 2580 93056
.empty
.empty)
.empty)
(.branch 2583 93082
.empty
.empty))
(.branch 2586 93153
(.branch 2585 93179
.empty
.empty)
(.branch 2587 93033
.empty
.empty)))
(.branch 2593 92915
(.branch 2591 92961
(.branch 2590 93225
(.branch 2589 93203
.empty
.empty)
.empty)
(.branch 2592 93275
.empty
.empty))
(.branch 2595 93249
(.branch 2594 92937
.empty
.empty)
(.branch 2596 93107
.empty
.empty))))
(.branch 2606 93250
(.branch 2602 93130
(.branch 2600 93080
(.branch 2599 93129
(.branch 2598 93057
.empty
.empty)
.empty)
(.branch 2601 93104
.empty
.empty))
(.branch 2604 92912
(.branch 2603 93058
.empty
.empty)
(.branch 2605 93272
.empty
.empty)))
(.branch 2611 93226
(.branch 2609 92984
(.branch 2608 93200
(.branch 2607 92938
.empty
.empty)
.empty)
(.branch 2610 92962
.empty
.empty))
(.branch 2613 93008
(.branch 2612 93176
.empty
.empty)
(.branch 2614 93034
.empty
.empty)))))
(.branch 2633 93032
(.branch 2624 92963
(.branch 2620 93251
(.branch 2618 93081
(.branch 2617 93059
(.branch 2616 93131
.empty
.empty)
.empty)
(.branch 2619 93105
.empty
.empty))
(.branch 2622 92913
(.branch 2621 92939
.empty
.empty)
(.branch 2623 93273
.empty
.empty)))
(.branch 2629 93155
(.branch 2627 92985
(.branch 2626 93201
(.branch 2625 93227
.empty
.empty)
.empty)
(.branch 2628 93035
.empty
.empty))
(.branch 2631 93009
(.branch 2630 93177
.empty
.empty)
(.branch 2632 93152
.empty
.empty))))
(.branch 2642 93274
(.branch 2638 92986
(.branch 2636 93224
(.branch 2635 93178
(.branch 2634 93010
.empty
.empty)
.empty)
(.branch 2637 92960
.empty
.empty))
(.branch 2640 92936
(.branch 2639 93202
.empty
.empty)
(.branch 2641 93248
.empty
.empty)))
(.branch 2647 93082
(.branch 2645 93128
(.branch 2644 93056
(.branch 2643 92914
.empty
.empty)
.empty)
(.branch 2646 93106
.empty
.empty))
(.branch 2649 93179
(.branch 2648 93011
.empty
.empty)
(.branch 2650 93153
.empty
.empty))))))
(.branch 2687 78729
(.branch 2669 78993
(.branch 2660 93107
(.branch 2656 93275
(.branch 2654 93225
(.branch 2653 93203
(.branch 2652 92987
.empty
.empty)
.empty)
(.branch 2655 92961
.empty
.empty))
(.branch 2658 92937
(.branch 2657 92915
.empty
.empty)
(.branch 2659 93249
.empty
.empty)))
(.branch 2665 78827
(.branch 2663 93129
(.branch 2662 93057
(.branch 2661 93083
.empty
.empty)
.empty)
(.branch 2664 78824
.empty
.empty))
(.branch 2667 78969
(.branch 2666 78970
.empty
.empty)
(.branch 2668 78994
.empty
.empty))))
(.branch 2678 78874
(.branch 2674 79040
(.branch 2672 78706
(.branch 2671 78755
(.branch 2670 78752
.empty
.empty)
.empty)
(.branch 2673 78705
.empty
.empty))
(.branch 2676 78920
(.branch 2675 79043
.empty
.empty)
(.branch 2677 78923
.empty
.empty)))
(.branch 2683 78899
(.branch 2681 78849
(.branch 2680 78850
(.branch 2679 78873
.empty
.empty)
.empty)
(.branch 2682 78896
.empty
.empty))
(.branch 2685 79067
(.branch 2684 79064
.empty
.empty)
(.branch 2686 78730
.empty
.empty)))))
(.branch 2705 78704
(.branch 2696 78825
(.branch 2692 78946
(.branch 2690 79018
(.branch 2689 78779
(.branch 2688 78776
.empty
.empty)
.empty)
(.branch 2691 79017
.empty
.empty))
(.branch 2694 78800
(.branch 2693 78945
.empty
.empty)
(.branch 2695 78803
.empty
.empty)))
(.branch 2701 78992
(.branch 2699 78968
(.branch 2698 78971
(.branch 2697 78826
.empty
.empty)
.empty)
(.branch 2700 78995
.empty
.empty))
(.branch 2703 78754
(.branch 2702 78753
.empty
.empty)
(.branch 2704 78707
.empty
.empty))))
(.branch 2714 78897
(.branch 2710 78875
(.branch 2708 78921
(.branch 2707 79042
(.branch 2706 79041
.empty
.empty)
.empty)
(.branch 2709 78922
.empty
.empty))
(.branch 2712 78851
(.branch 2711 78872
.empty
.empty)
(.branch 2713 78848
.empty
.empty)))
(.branch 2718 78731
(.branch 2716 79065
(.branch 2715 78898
.empty
.empty)
(.branch 2717 79066
.empty
.empty))
(.branch 2720 78777
(.branch 2719 78728
.empty
.empty)
(.branch 2721 78778
.empty
.empty)))))))
(.branch 2794 88873
(.branch 2758 78800
(.branch 2740 78920
(.branch 2731 78969
(.branch 2727 78802
(.branch 2725 78944
(.branch 2724 78947
(.branch 2723 79016
.empty
.empty)
.empty)
(.branch 2726 78801
.empty
.empty))
(.branch 2729 78827
(.branch 2728 78824
.empty
.empty)
(.branch 2730 78970
.empty
.empty)))
(.branch 2736 78706
(.branch 2734 78752
(.branch 2733 78993
(.branch 2732 78994
.empty
.empty)
.empty)
(.branch 2735 78755
.empty
.empty))
(.branch 2738 79040
(.branch 2737 78705
.empty
.empty)
(.branch 2739 79043
.empty
.empty))))
(.branch 2749 79067
(.branch 2745 78849
(.branch 2743 78873
(.branch 2742 78874
(.branch 2741 78923
.empty
.empty)
.empty)
(.branch 2744 78850
.empty
.empty))
(.branch 2747 78899
(.branch 2746 78896
.empty
.empty)
(.branch 2748 79064
.empty
.empty)))
(.branch 2754 79018
(.branch 2752 78776
(.branch 2751 78729
(.branch 2750 78730
.empty
.empty)
.empty)
(.branch 2753 78779
.empty
.empty))
(.branch 2756 78946
(.branch 2755 79017
.empty
.empty)
(.branch 2757 78945
.empty
.empty)))))
(.branch 2776 78851
(.branch 2767 78754
(.branch 2763 78968
(.branch 2761 78826
(.branch 2760 78825
(.branch 2759 78803
.empty
.empty)
.empty)
(.branch 2762 78971
.empty
.empty))
(.branch 2765 78992
(.branch 2764 78995
.empty
.empty)
(.branch 2766 78753
.empty
.empty)))
(.branch 2772 78921
(.branch 2770 79041
(.branch 2769 78704
(.branch 2768 78707
.empty
.empty)
.empty)
(.branch 2771 79042
.empty
.empty))
(.branch 2774 78875
(.branch 2773 78922
.empty
.empty)
(.branch 2775 78872
.empty
.empty))))
(.branch 2785 78778
(.branch 2781 79066
(.branch 2779 78898
(.branch 2778 78897
(.branch 2777 78848
.empty
.empty)
.empty)
(.branch 2780 79065
.empty
.empty))
(.branch 2783 78728
(.branch 2782 78731
.empty
.empty)
(.branch 2784 78777
.empty
.empty)))
(.branch 2790 78801
(.branch 2788 78947
(.branch 2787 79016
(.branch 2786 79019
.empty
.empty)
.empty)
(.branch 2789 78944
.empty
.empty))
(.branch 2792 88945
(.branch 2791 78802
.empty
.empty)
(.branch 2793 88920
.empty
.empty))))))
(.branch 2830 89041
(.branch 2812 88754
(.branch 2803 88968
(.branch 2799 88680
(.branch 2797 88752
(.branch 2796 88729
(.branch 2795 88896
.empty
.empty)
.empty)
(.branch 2798 88705
.empty
.empty))
(.branch 2801 89040
(.branch 2800 89017
.empty
.empty)
(.branch 2802 88993
.empty
.empty)))
(.branch 2808 88922
(.branch 2806 88777
(.branch 2805 88824
(.branch 2804 88849
.empty
.empty)
.empty)
(.branch 2807 88800
.empty
.empty))
(.branch 2810 88898
(.branch 2809 88947
.empty
.empty)
(.branch 2811 88875
.empty
.empty))))
(.branch 2821 88851
(.branch 2817 89019
(.branch 2815 88707
(.branch 2814 88682
(.branch 2813 88731
.empty
.empty)
.empty)
(.branch 2816 89042
.empty
.empty))
(.branch 2819 88995
(.branch 2818 88970
.empty
.empty)
(.branch 2820 88826
.empty
.empty)))
(.branch 2826 88825
(.branch 2824 88801
(.branch 2823 88779
(.branch 2822 88802
.empty
.empty)
.empty)
(.branch 2825 88776
.empty
.empty))
(.branch 2828 88969
(.branch 2827 88848
.empty
.empty)
(.branch 2829 88992
.empty
.empty)))))
(.branch 2848 88706
(.branch 2839 88944
(.branch 2835 88728
(.branch 2833 88704
(.branch 2832 88681
(.branch 2831 89016
.empty
.empty)
.empty)
(.branch 2834 88753
.empty
.empty))
(.branch 2837 88872
(.branch 2836 88897
.empty
.empty)
(.branch 2838 88921
.empty
.empty)))
(.branch 2844 88994
(.branch 2842 88850
(.branch 2841 88803
(.branch 2840 88778
.empty
.empty)
.empty)
(.branch 2843 88827
.empty
.empty))
(.branch 2846 89018
(.branch 2845 88971
.empty
.empty)
(.branch 2847 89043
.empty
.empty))))
(.branch 2857 88920
(.branch 2853 88899
(.branch 2851 88755
(.branch 2850 88730
(.branch 2849 88683
.empty
.empty)
.empty)
(.branch 2852 88874
.empty
.empty))
(.branch 2855 88923
(.branch 2854 88946
.empty
.empty)
(.branch 2856 88945
.empty
.empty)))
(.branch 2861 88752
(.branch 2859 88896
(.branch 2858 88873
.empty
.empty)
(.branch 2860 88729
.empty
.empty))
(.branch 2863 88680
(.branch 2862 88705
.empty
.empty)
(.branch 2864 89017
.empty
.empty)))))))))
(.branch 3152 83096
(.branch 3009 83280
(.branch 2937 83136
(.branch 2901 88872
(.branch 2883 88995
(.branch 2874 88898
(.branch 2870 88777
(.branch 2868 88849
(.branch 2867 88968
(.branch 2866 88993
.empty
.empty)
.empty)
(.branch 2869 88824
.empty
.empty))
(.branch 2872 88922
(.branch 2871 88800
.empty
.empty)
(.branch 2873 88947
.empty
.empty)))
(.branch 2879 88707
(.branch 2877 88731
(.branch 2876 88754
(.branch 2875 88875
.empty
.empty)
.empty)
(.branch 2878 88682
.empty
.empty))
(.branch 2881 89019
(.branch 2880 89042
.empty
.empty)
(.branch 2882 88970
.empty
.empty))))
(.branch 2892 88969
(.branch 2888 88801
(.branch 2886 88802
(.branch 2885 88851
(.branch 2884 88826
.empty
.empty)
.empty)
(.branch 2887 88779
.empty
.empty))
(.branch 2890 88825
(.branch 2889 88776
.empty
.empty)
(.branch 2891 88848
.empty
.empty)))
(.branch 2897 88704
(.branch 2895 89016
(.branch 2894 89041
(.branch 2893 88992
.empty
.empty)
.empty)
(.branch 2896 88681
.empty
.empty))
(.branch 2899 88728
(.branch 2898 88753
.empty
.empty)
(.branch 2900 88897
.empty
.empty)))))
(.branch 2919 88923
(.branch 2910 89018
(.branch 2906 88850
(.branch 2904 88778
(.branch 2903 88944
(.branch 2902 88921
.empty
.empty)
.empty)
(.branch 2905 88803
.empty
.empty))
(.branch 2908 88994
(.branch 2907 88827
.empty
.empty)
(.branch 2909 88971
.empty
.empty)))
(.branch 2915 88755
(.branch 2913 88683
(.branch 2912 88706
(.branch 2911 89043
.empty
.empty)
.empty)
(.branch 2914 88730
.empty
.empty))
(.branch 2917 88899
(.branch 2916 88874
.empty
.empty)
(.branch 2918 88946
.empty
.empty))))
(.branch 2928 83281
(.branch 2924 82993
(.branch 2922 83161
(.branch 2921 83187
(.branch 2920 83137
.empty
.empty)
.empty)
(.branch 2923 83115
.empty
.empty))
(.branch 2926 82921
(.branch 2925 82947
.empty
.empty)
(.branch 2927 82971
.empty
.empty)))
(.branch 2933 83091
(.branch 2931 83259
(.branch 2930 83209
(.branch 2929 83235
.empty
.empty)
.empty)
(.branch 2932 83041
.empty
.empty))
(.branch 2935 83019
(.branch 2934 83065
.empty
.empty)
(.branch 2936 83186
.empty
.empty))))))
(.branch 2973 83256
(.branch 2955 83043
(.branch 2946 83258
(.branch 2942 82970
(.branch 2940 82946
(.branch 2939 83160
(.branch 2938 83114
.empty
.empty)
.empty)
(.branch 2941 82992
.empty
.empty))
(.branch 2944 83234
(.branch 2943 82920
.empty
.empty)
(.branch 2945 83280
.empty
.empty)))
(.branch 2951 83064
(.branch 2949 83040
(.branch 2948 83090
(.branch 2947 83208
.empty
.empty)
.empty)
(.branch 2950 83018
.empty
.empty))
(.branch 2953 83067
(.branch 2952 83017
.empty
.empty)
(.branch 2954 83089
.empty
.empty))))
(.branch 2964 83113
(.branch 2960 82969
(.branch 2958 83233
(.branch 2957 83211
(.branch 2956 83257
.empty
.empty)
.empty)
(.branch 2959 83283
.empty
.empty))
(.branch 2962 82945
(.branch 2961 82923
.empty
.empty)
(.branch 2963 82995
.empty
.empty)))
(.branch 2969 83016
(.branch 2967 83139
(.branch 2966 83185
(.branch 2965 83163
.empty
.empty)
.empty)
(.branch 2968 83066
.empty
.empty))
(.branch 2971 83088
(.branch 2970 83042
.empty
.empty)
(.branch 2972 83210
.empty
.empty)))))
(.branch 2991 82971
(.branch 2982 83138
(.branch 2978 82994
(.branch 2976 82922
(.branch 2975 83232
(.branch 2974 83282
.empty
.empty)
.empty)
(.branch 2977 82968
.empty
.empty))
(.branch 2980 83162
(.branch 2979 82944
.empty
.empty)
(.branch 2981 83112
.empty
.empty)))
(.branch 2987 83115
(.branch 2985 83187
(.branch 2984 83137
(.branch 2983 83184
.empty
.empty)
.empty)
(.branch 2986 83161
.empty
.empty))
(.branch 2989 82947
(.branch 2988 82993
.empty
.empty)
(.branch 2990 82921
.empty
.empty))))
(.branch 3000 83186
(.branch 2996 83041
(.branch 2994 83209
(.branch 2993 83235
(.branch 2992 83281
.empty
.empty)
.empty)
(.branch 2995 83259
.empty
.empty))
(.branch 2998 83065
(.branch 2997 83091
.empty
.empty)
(.branch 2999 83019
.empty
.empty)))
(.branch 3005 82992
(.branch 3003 83160
(.branch 3002 83114
(.branch 3001 83136
.empty
.empty)
.empty)
(.branch 3004 82946
.empty
.empty))
(.branch 3007 82920
(.branch 3006 82970
.empty
.empty)
(.branch 3008 83234
.empty
.empty)))))))
(.branch 3081 82928
(.branch 3045 83112
(.branch 3027 82995
(.branch 3018 83089
(.branch 3014 83018
(.branch 3012 83090
(.branch 3011 83208
(.branch 3010 83258
.empty
.empty)
.empty)
(.branch 3013 83040
.empty
.empty))
(.branch 3016 83017
(.branch 3015 83064
.empty
.empty)
(.branch 3017 83067
.empty
.empty)))
(.branch 3023 83283
(.branch 3021 83211
(.branch 3020 83257
(.branch 3019 83043
.empty
.empty)
.empty)
(.branch 3022 83233
.empty
.empty))
(.branch 3025 82923
(.branch 3024 82969
.empty
.empty)
(.branch 3026 82945
.empty
.empty))))
(.branch 3036 83210
(.branch 3032 83066
(.branch 3030 83185
(.branch 3029 83163
(.branch 3028 83113
.empty
.empty)
.empty)
(.branch 3031 83139
.empty
.empty))
(.branch 3034 83042
(.branch 3033 83016
.empty
.empty)
(.branch 3035 83088
.empty
.empty)))
(.branch 3041 82968
(.branch 3039 83232
(.branch 3038 83282
(.branch 3037 83256
.empty
.empty)
.empty)
(.branch 3040 82922
.empty
.empty))
(.branch 3043 82944
(.branch 3042 82994
.empty
.empty)
(.branch 3044 83162
.empty
.empty)))))
(.branch 3063 83169
(.branch 3054 83241
(.branch 3050 83243
(.branch 3048 83120
(.branch 3047 83184
(.branch 3046 83138
.empty
.empty)
.empty)
(.branch 3049 82955
.empty
.empty))
(.branch 3052 83122
(.branch 3051 83024
.empty
.empty)
(.branch 3053 82953
.empty
.empty)))
(.branch 3059 83171
(.branch 3057 83288
(.branch 3056 83075
(.branch 3055 83026
.empty
.empty)
.empty)
(.branch 3058 83000
.empty
.empty))
(.branch 3061 83290
(.branch 3060 83073
.empty
.empty)
(.branch 3062 83002
.empty
.empty))))
(.branch 3072 83074
(.branch 3068 83123
(.branch 3066 83242
(.branch 3065 82954
(.branch 3064 83121
.empty
.empty)
.empty)
(.branch 3067 83025
.empty
.empty))
(.branch 3070 83240
(.branch 3069 82952
.empty
.empty)
(.branch 3071 83027
.empty
.empty)))
(.branch 3077 83291
(.branch 3075 83170
(.branch 3074 83001
(.branch 3073 83289
.empty
.empty)
.empty)
(.branch 3076 83072
.empty
.empty))
(.branch 3079 83168
(.branch 3078 83003
.empty
.empty)
(.branch 3080 83147
.empty
.empty))))))
(.branch 3117 82953
(.branch 3099 83050
(.branch 3090 82979
(.branch 3086 83218
(.branch 3084 83145
(.branch 3083 83051
(.branch 3082 83216
.empty
.empty)
.empty)
(.branch 3085 82930
.empty
.empty))
(.branch 3088 83096
(.branch 3087 83049
.empty
.empty)
(.branch 3089 83267
.empty
.empty)))
(.branch 3095 83194
(.branch 3093 83265
(.branch 3092 83098
(.branch 3091 83192
.empty
.empty)
.empty)
(.branch 3094 82977
.empty
.empty))
(.branch 3097 82929
(.branch 3096 83146
.empty
.empty)
(.branch 3098 83217
.empty
.empty))))
(.branch 3108 83099
(.branch 3104 83097
(.branch 3102 83219
(.branch 3101 82931
(.branch 3100 83144
.empty
.empty)
.empty)
(.branch 3103 83048
.empty
.empty))
(.branch 3106 82978
(.branch 3105 83266
.empty
.empty)
(.branch 3107 83193
.empty
.empty)))
(.branch 3113 82955
(.branch 3111 83195
(.branch 3110 82976
(.branch 3109 83264
.empty
.empty)
.empty)
(.branch 3112 83120
.empty
.empty))
(.branch 3115 83024
(.branch 3114 83243
.empty
.empty)
(.branch 3116 83122
.empty
.empty)))))
(.branch 3135 83027
(.branch 3126 83002
(.branch 3122 83000
(.branch 3120 83075
(.branch 3119 83026
(.branch 3118 83241
.empty
.empty)
.empty)
(.branch 3121 83288
.empty
.empty))
(.branch 3124 83073
(.branch 3123 83171
.empty
.empty)
(.branch 3125 83290
.empty
.empty)))
(.branch 3131 83025
(.branch 3129 82954
(.branch 3128 83121
(.branch 3127 83169
.empty
.empty)
.empty)
(.branch 3130 83242
.empty
.empty))
(.branch 3133 82952
(.branch 3132 83123
.empty
.empty)
(.branch 3134 83240
.empty
.empty))))
(.branch 3144 83147
(.branch 3140 83072
(.branch 3138 83001
(.branch 3137 83289
(.branch 3136 83074
.empty
.empty)
.empty)
(.branch 3139 83170
.empty
.empty))
(.branch 3142 83003
(.branch 3141 83291
.empty
.empty)
(.branch 3143 83168
.empty
.empty)))
(.branch 3148 83145
(.branch 3146 83216
(.branch 3145 82928
.empty
.empty)
(.branch 3147 83051
.empty
.empty))
(.branch 3150 83218
(.branch 3149 82930
.empty
.empty)
(.branch 3151 83049
.empty
.empty))))))))
(.branch 3295 88712
(.branch 3224 88954
(.branch 3188 88832
(.branch 3170 82978
(.branch 3161 82929
(.branch 3157 83265
(.branch 3155 83192
(.branch 3154 82979
(.branch 3153 83267
.empty
.empty)
.empty)
(.branch 3156 83098
.empty
.empty))
(.branch 3159 83194
(.branch 3158 82977
.empty
.empty)
(.branch 3160 83146
.empty
.empty)))
(.branch 3166 83219
(.branch 3164 83144
(.branch 3163 83050
(.branch 3162 83217
.empty
.empty)
.empty)
(.branch 3165 82931
.empty
.empty))
(.branch 3168 83097
(.branch 3167 83048
.empty
.empty)
(.branch 3169 83266
.empty
.empty))))
(.branch 3179 88907
(.branch 3175 83195
(.branch 3173 83264
(.branch 3172 83099
(.branch 3171 83193
.empty
.empty)
.empty)
(.branch 3174 82976
.empty
.empty))
(.branch 3177 88930
(.branch 3176 88928
.empty
.empty)
(.branch 3178 88905
.empty
.empty)))
(.branch 3184 89049
(.branch 3182 88688
(.branch 3181 88763
(.branch 3180 88761
.empty
.empty)
.empty)
(.branch 3183 88690
.empty
.empty))
(.branch 3186 88976
(.branch 3185 89051
.empty
.empty)
(.branch 3187 88978
.empty
.empty)))))
(.branch 3206 88810
(.branch 3197 88760
(.branch 3193 88929
(.branch 3191 88811
(.branch 3190 88809
(.branch 3189 88834
.empty
.empty)
.empty)
(.branch 3192 88931
.empty
.empty))
(.branch 3195 88904
(.branch 3194 88906
.empty
.empty)
(.branch 3196 88762
.empty
.empty)))
(.branch 3202 88979
(.branch 3200 89050
(.branch 3199 88689
(.branch 3198 88691
.empty
.empty)
.empty)
(.branch 3201 89048
.empty
.empty))
(.branch 3204 88835
(.branch 3203 88977
.empty
.empty)
(.branch 3205 88833
.empty
.empty))))
(.branch 3215 88715
(.branch 3211 88882
(.branch 3209 88955
(.branch 3208 88953
(.branch 3207 88808
.empty
.empty)
.empty)
(.branch 3210 88880
.empty
.empty))
(.branch 3213 88738
(.branch 3212 88736
.empty
.empty)
(.branch 3214 88713
.empty
.empty)))
(.branch 3220 88857
(.branch 3218 89001
(.branch 3217 89026
(.branch 3216 89024
.empty
.empty)
.empty)
(.branch 3219 89003
.empty
.empty))
(.branch 3222 88784
(.branch 3221 88859
.empty
.empty)
(.branch 3223 88786
.empty
.empty))))))
(.branch 3260 88762
(.branch 3242 88905
(.branch 3233 89025
(.branch 3229 88737
(.branch 3227 88881
(.branch 3226 88883
(.branch 3225 88952
.empty
.empty)
.empty)
(.branch 3228 88739
.empty
.empty))
(.branch 3231 88712
(.branch 3230 88714
.empty
.empty)
(.branch 3232 89027
.empty
.empty)))
(.branch 3238 88787
(.branch 3236 88858
(.branch 3235 89000
(.branch 3234 89002
.empty
.empty)
.empty)
(.branch 3237 88856
.empty
.empty))
(.branch 3240 88928
(.branch 3239 88785
.empty
.empty)
(.branch 3241 88930
.empty
.empty))))
(.branch 3251 88978
(.branch 3247 88690
(.branch 3245 88763
(.branch 3244 88761
(.branch 3243 88907
.empty
.empty)
.empty)
(.branch 3246 88688
.empty
.empty))
(.branch 3249 89051
(.branch 3248 89049
.empty
.empty)
(.branch 3250 88976
.empty
.empty)))
(.branch 3256 88931
(.branch 3254 88809
(.branch 3253 88834
(.branch 3252 88832
.empty
.empty)
.empty)
(.branch 3255 88811
.empty
.empty))
(.branch 3258 88906
(.branch 3257 88929
.empty
.empty)
(.branch 3259 88904
.empty
.empty)))))
(.branch 3278 88713
(.branch 3269 88833
(.branch 3265 89048
(.branch 3263 88689
(.branch 3262 88691
(.branch 3261 88760
.empty
.empty)
.empty)
(.branch 3264 89050
.empty
.empty))
(.branch 3267 88977
(.branch 3266 88979
.empty
.empty)
(.branch 3268 88835
.empty
.empty)))
(.branch 3274 88880
(.branch 3272 88953
(.branch 3271 88808
(.branch 3270 88810
.empty
.empty)
.empty)
(.branch 3273 88955
.empty
.empty))
(.branch 3276 88736
(.branch 3275 88882
.empty
.empty)
(.branch 3277 88738
.empty
.empty))))
(.branch 3287 88786
(.branch 3283 89003
(.branch 3281 89026
(.branch 3280 89024
(.branch 3279 88715
.empty
.empty)
.empty)
(.branch 3282 89001
.empty
.empty))
(.branch 3285 88859
(.branch 3284 88857
.empty
.empty)
(.branch 3286 88784
.empty
.empty)))
(.branch 3291 88881
(.branch 3289 88952
(.branch 3288 88954
.empty
.empty)
(.branch 3290 88883
.empty
.empty))
(.branch 3293 88737
(.branch 3292 88739
.empty
.empty)
(.branch 3294 88714
.empty
.empty)))))))
(.branch 3367 78840
(.branch 3331 79034
(.branch 3313 78698
(.branch 3304 78793
(.branch 3300 88858
(.branch 3298 89002
(.branch 3297 89025
(.branch 3296 89027
.empty
.empty)
.empty)
(.branch 3299 89000
.empty
.empty))
(.branch 3302 88787
(.branch 3301 88856
.empty
.empty)
(.branch 3303 88785
.empty
.empty)))
(.branch 3309 78986
(.branch 3307 78962
(.branch 3306 78913
(.branch 3305 78842
.empty
.empty)
.empty)
(.branch 3308 79033
.empty
.empty))
(.branch 3311 78722
(.branch 3310 78769
.empty
.empty)
(.branch 3312 78745
.empty
.empty))))
(.branch 3322 78937
(.branch 3318 78817
(.branch 3316 78889
(.branch 3315 79010
(.branch 3314 79057
.empty
.empty)
.empty)
(.branch 3317 78938
.empty
.empty))
(.branch 3320 78865
(.branch 3319 78866
.empty
.empty)
(.branch 3321 78818
.empty
.empty)))
(.branch 3327 78746
(.branch 3325 79058
(.branch 3324 79009
(.branch 3323 78890
.empty
.empty)
.empty)
(.branch 3326 78697
.empty
.empty))
(.branch 3329 78770
(.branch 3328 78721
.empty
.empty)
(.branch 3330 78985
.empty
.empty)))))
(.branch 3349 78888
(.branch 3340 78987
(.branch 3336 78843
(.branch 3334 78841
(.branch 3333 78914
(.branch 3332 78961
.empty
.empty)
.empty)
(.branch 3335 78794
.empty
.empty))
(.branch 3338 78963
(.branch 3337 78792
.empty
.empty)
(.branch 3339 78912
.empty
.empty)))
(.branch 3345 78744
(.branch 3343 78768
(.branch 3342 78723
(.branch 3341 79032
.empty
.empty)
.empty)
(.branch 3344 78699
.empty
.empty))
(.branch 3347 79056
(.branch 3346 79011
.empty
.empty)
(.branch 3348 78939
.empty
.empty))))
(.branch 3358 78747
(.branch 3354 78891
(.branch 3352 78819
(.branch 3351 78816
(.branch 3350 78867
.empty
.empty)
.empty)
(.branch 3353 78864
.empty
.empty))
(.branch 3356 79059
(.branch 3355 78936
.empty
.empty)
(.branch 3357 79008
.empty
.empty)))
(.branch 3363 78984
(.branch 3361 78720
(.branch 3360 78771
(.branch 3359 78696
.empty
.empty)
.empty)
(.branch 3362 79035
.empty
.empty))
(.branch 3365 78960
(.branch 3364 78915
.empty
.empty)
(.branch 3366 78795
.empty
.empty))))))
(.branch 3403 78912
(.branch 3385 78818
(.branch 3376 78745
(.branch 3372 79033
(.branch 3370 78913
(.branch 3369 78842
(.branch 3368 78793
.empty
.empty)
.empty)
(.branch 3371 78962
.empty
.empty))
(.branch 3374 78769
(.branch 3373 78986
.empty
.empty)
(.branch 3375 78722
.empty
.empty)))
(.branch 3381 78938
(.branch 3379 79010
(.branch 3378 79057
(.branch 3377 78698
.empty
.empty)
.empty)
(.branch 3380 78889
.empty
.empty))
(.branch 3383 78866
(.branch 3382 78817
.empty
.empty)
(.branch 3384 78865
.empty
.empty))))
(.branch 3394 78985
(.branch 3390 78697
(.branch 3388 79009
(.branch 3387 78890
(.branch 3386 78937
.empty
.empty)
.empty)
(.branch 3389 79058
.empty
.empty))
(.branch 3392 78721
(.branch 3391 78746
.empty
.empty)
(.branch 3393 78770
.empty
.empty)))
(.branch 3399 78794
(.branch 3397 78914
(.branch 3396 78961
(.branch 3395 79034
.empty
.empty)
.empty)
(.branch 3398 78841
.empty
.empty))
(.branch 3401 78792
(.branch 3400 78843
.empty
.empty)
(.branch 3402 78963
.empty
.empty)))))
(.branch 3421 79008
(.branch 3412 78939
(.branch 3408 78699
(.branch 3406 78723
(.branch 3405 79032
(.branch 3404 78987
.empty
.empty)
.empty)
(.branch 3407 78768
.empty
.empty))
(.branch 3410 79011
(.branch 3409 78744
.empty
.empty)
(.branch 3411 79056
.empty
.empty)))
(.branch 3417 78864
(.branch 3415 78816
(.branch 3414 78867
(.branch 3413 78888
.empty
.empty)
.empty)
(.branch 3416 78819
.empty
.empty))
(.branch 3419 78936
(.branch 3418 78891
.empty
.empty)
(.branch 3420 79059
.empty
.empty))))
(.branch 3430 78795
(.branch 3426 79035
(.branch 3424 78771
(.branch 3423 78696
(.branch 3422 78747
.empty
.empty)
.empty)
(.branch 3425 78720
.empty
.empty))
(.branch 3428 78915
(.branch 3427 78984
.empty
.empty)
(.branch 3429 78960
.empty
.empty)))
(.branch 3434 93217
(.branch 3432 93049
(.branch 3431 78840
.empty
.empty)
(.branch 3433 92929
.empty
.empty))
(.branch 3436 93120
(.branch 3435 93145
.empty
.empty)
(.branch 3437 93240
.empty
.empty))))))))))
(.branch 4011 78871
(.branch 3725 83295
(.branch 3582 89028
(.branch 3510 93264
(.branch 3474 93267
(.branch 3456 93025
(.branch 3447 93096
(.branch 3443 93073
(.branch 3441 93193
(.branch 3440 93169
(.branch 3439 93024
.empty
.empty)
.empty)
(.branch 3442 92905
.empty
.empty))
(.branch 3445 92976
(.branch 3444 93000
.empty
.empty)
(.branch 3446 93264
.empty
.empty)))
(.branch 3452 93072
(.branch 3450 92977
(.branch 3449 93265
(.branch 3448 93097
.empty
.empty)
.empty)
(.branch 3451 93001
.empty
.empty))
(.branch 3454 93192
(.branch 3453 92904
.empty
.empty)
(.branch 3455 93168
.empty
.empty))))
(.branch 3465 93243
(.branch 3461 93216
(.branch 3459 93121
(.branch 3458 93241
(.branch 3457 92953
.empty
.empty)
.empty)
(.branch 3460 93144
.empty
.empty))
(.branch 3463 93048
(.branch 3462 92928
.empty
.empty)
(.branch 3464 93123
.empty
.empty)))
(.branch 3470 93218
(.branch 3468 93050
(.branch 3467 93027
(.branch 3466 92955
.empty
.empty)
.empty)
(.branch 3469 92930
.empty
.empty))
(.branch 3472 93003
(.branch 3471 93146
.empty
.empty)
(.branch 3473 92979
.empty
.empty)))))
(.branch 3492 93026
(.branch 3483 93171
(.branch 3479 93074
(.branch 3477 93194
(.branch 3476 93170
(.branch 3475 93099
.empty
.empty)
.empty)
(.branch 3478 92906
.empty
.empty))
(.branch 3481 92907
(.branch 3480 93075
.empty
.empty)
(.branch 3482 93195
.empty
.empty)))
(.branch 3488 93147
(.branch 3486 92978
(.branch 3485 93266
(.branch 3484 93098
.empty
.empty)
.empty)
(.branch 3487 93002
.empty
.empty))
(.branch 3490 92931
(.branch 3489 93219
.empty
.empty)
(.branch 3491 93051
.empty
.empty))))
(.branch 3501 93240
(.branch 3497 92929
(.branch 3495 93122
(.branch 3494 93242
(.branch 3493 92954
.empty
.empty)
.empty)
(.branch 3496 93049
.empty
.empty))
(.branch 3499 93145
(.branch 3498 93217
.empty
.empty)
(.branch 3500 93120
.empty
.empty)))
(.branch 3506 92905
(.branch 3504 93169
(.branch 3503 93024
(.branch 3502 92952
.empty
.empty)
.empty)
(.branch 3505 93193
.empty
.empty))
(.branch 3508 93000
(.branch 3507 93073
.empty
.empty)
(.branch 3509 92976
.empty
.empty))))))
(.branch 3546 93195
(.branch 3528 93123
(.branch 3519 93168
(.branch 3515 93001
(.branch 3513 93265
(.branch 3512 93097
(.branch 3511 93096
.empty
.empty)
.empty)
(.branch 3514 92977
.empty
.empty))
(.branch 3517 92904
(.branch 3516 93072
.empty
.empty)
(.branch 3518 93192
.empty
.empty)))
(.branch 3524 93144
(.branch 3522 93241
(.branch 3521 92953
(.branch 3520 93025
.empty
.empty)
.empty)
(.branch 3523 93121
.empty
.empty))
(.branch 3526 92928
(.branch 3525 93216
.empty
.empty)
(.branch 3527 93048
.empty
.empty))))
(.branch 3537 92979
(.branch 3533 92930
(.branch 3531 93027
(.branch 3530 92955
(.branch 3529 93243
.empty
.empty)
.empty)
(.branch 3532 93050
.empty
.empty))
(.branch 3535 93146
(.branch 3534 93218
.empty
.empty)
(.branch 3536 93003
.empty
.empty)))
(.branch 3542 92906
(.branch 3540 93170
(.branch 3539 93099
(.branch 3538 93267
.empty
.empty)
.empty)
(.branch 3541 93194
.empty
.empty))
(.branch 3544 93075
(.branch 3543 93074
.empty
.empty)
(.branch 3545 92907
.empty
.empty)))))
(.branch 3564 88886
(.branch 3555 93051
(.branch 3551 93002
(.branch 3549 93266
(.branch 3548 93098
(.branch 3547 93171
.empty
.empty)
.empty)
(.branch 3550 92978
.empty
.empty))
(.branch 3553 93219
(.branch 3552 93147
.empty
.empty)
(.branch 3554 92931
.empty
.empty)))
(.branch 3560 88910
(.branch 3558 93242
(.branch 3557 92954
(.branch 3556 93026
.empty
.empty)
.empty)
(.branch 3559 93122
.empty
.empty))
(.branch 3562 88982
(.branch 3561 88694
.empty
.empty)
(.branch 3563 88814
.empty
.empty))))
(.branch 3573 88743
(.branch 3569 88767
(.branch 3567 88790
(.branch 3566 89006
(.branch 3565 88718
.empty
.empty)
.empty)
(.branch 3568 88935
.empty
.empty))
(.branch 3571 88839
(.branch 3570 89055
.empty
.empty)
(.branch 3572 88959
.empty
.empty)))
(.branch 3578 89052
(.branch 3576 88932
(.branch 3575 88863
(.branch 3574 89031
.empty
.empty)
.empty)
(.branch 3577 88764
.empty
.empty))
(.branch 3580 88956
(.branch 3579 88836
.empty
.empty)
(.branch 3581 88740
.empty
.empty)))))))
(.branch 3654 89005
(.branch 3618 88741
(.branch 3600 88791
(.branch 3591 88789
(.branch 3587 88813
(.branch 3585 88693
(.branch 3584 88909
(.branch 3583 88860
.empty
.empty)
.empty)
(.branch 3586 88981
.empty
.empty))
(.branch 3589 88717
(.branch 3588 88885
.empty
.empty)
(.branch 3590 89005
.empty
.empty)))
(.branch 3596 88838
(.branch 3594 88742
(.branch 3593 89030
(.branch 3592 88862
.empty
.empty)
.empty)
(.branch 3595 88958
.empty
.empty))
(.branch 3598 88766
(.branch 3597 89054
.empty
.empty)
(.branch 3599 88934
.empty
.empty))))
(.branch 3609 89004
(.branch 3605 88983
(.branch 3603 88887
(.branch 3602 88719
(.branch 3601 89007
.empty
.empty)
.empty)
(.branch 3604 88815
.empty
.empty))
(.branch 3607 88911
(.branch 3606 88695
.empty
.empty)
(.branch 3608 88788
.empty
.empty)))
(.branch 3614 88692
(.branch 3612 88812
(.branch 3611 88884
(.branch 3610 88716
.empty
.empty)
.empty)
(.branch 3613 88980
.empty
.empty))
(.branch 3616 88861
(.branch 3615 88908
.empty
.empty)
(.branch 3617 89029
.empty
.empty)))))
(.branch 3636 88959
(.branch 3627 88814
(.branch 3623 88933
(.branch 3621 89053
(.branch 3620 88837
(.branch 3619 88957
.empty
.empty)
.empty)
(.branch 3622 88765
.empty
.empty))
(.branch 3625 88694
(.branch 3624 88910
.empty
.empty)
(.branch 3626 88982
.empty
.empty)))
(.branch 3632 88935
(.branch 3630 89006
(.branch 3629 88718
(.branch 3628 88886
.empty
.empty)
.empty)
(.branch 3631 88790
.empty
.empty))
(.branch 3634 89055
(.branch 3633 88767
.empty
.empty)
(.branch 3635 88839
.empty
.empty))))
(.branch 3645 88740
(.branch 3641 88764
(.branch 3639 88863
(.branch 3638 89031
(.branch 3637 88743
.empty
.empty)
.empty)
(.branch 3640 88932
.empty
.empty))
(.branch 3643 88836
(.branch 3642 89052
.empty
.empty)
(.branch 3644 88956
.empty
.empty)))
(.branch 3650 88981
(.branch 3648 88909
(.branch 3647 88860
(.branch 3646 89028
.empty
.empty)
.empty)
(.branch 3649 88693
.empty
.empty))
(.branch 3652 88885
(.branch 3651 88813
.empty
.empty)
(.branch 3653 88717
.empty
.empty))))))
(.branch 3690 83196
(.branch 3672 88788
(.branch 3663 88934
(.branch 3659 88958
(.branch 3657 89030
(.branch 3656 88862
(.branch 3655 88789
.empty
.empty)
.empty)
(.branch 3658 88742
.empty
.empty))
(.branch 3661 89054
(.branch 3660 88838
.empty
.empty)
(.branch 3662 88766
.empty
.empty)))
(.branch 3668 88815
(.branch 3666 88719
(.branch 3665 89007
(.branch 3664 88791
.empty
.empty)
.empty)
(.branch 3667 88887
.empty
.empty))
(.branch 3670 88695
(.branch 3669 88983
.empty
.empty)
(.branch 3671 88911
.empty
.empty))))
(.branch 3681 89029
(.branch 3677 88980
(.branch 3675 88884
(.branch 3674 88716
(.branch 3673 89004
.empty
.empty)
.empty)
(.branch 3676 88812
.empty
.empty))
(.branch 3679 88908
(.branch 3678 88692
.empty
.empty)
(.branch 3680 88861
.empty
.empty)))
(.branch 3686 88765
(.branch 3684 88837
(.branch 3683 88957
(.branch 3682 88741
.empty
.empty)
.empty)
(.branch 3685 89053
.empty
.empty))
(.branch 3688 83198
(.branch 3687 88933
.empty
.empty)
(.branch 3689 83127
.empty
.empty)))))
(.branch 3708 82956
(.branch 3699 83268
(.branch 3695 82980
(.branch 3693 82982
(.branch 3692 82959
(.branch 3691 83125
.empty
.empty)
.empty)
(.branch 3694 82957
.empty
.empty))
(.branch 3697 83270
(.branch 3696 83247
.empty
.empty)
(.branch 3698 83245
.empty
.empty)))
(.branch 3704 83197
(.branch 3702 83100
(.branch 3701 83031
(.branch 3700 83102
.empty
.empty)
.empty)
(.branch 3703 83029
.empty
.empty))
(.branch 3706 83199
(.branch 3705 83124
.empty
.empty)
(.branch 3707 83126
.empty
.empty))))
(.branch 3717 83028
(.branch 3713 83269
(.branch 3711 82983
(.branch 3710 82958
(.branch 3709 82981
.empty
.empty)
.empty)
(.branch 3712 83244
.empty
.empty))
(.branch 3715 83271
(.branch 3714 83246
.empty
.empty)
(.branch 3716 83101
.empty
.empty)))
(.branch 3721 83054
(.branch 3719 83030
(.branch 3718 83103
.empty
.empty)
(.branch 3720 83079
.empty
.empty))
(.branch 3723 83052
(.branch 3722 83077
.empty
.empty)
(.branch 3724 83222
.empty
.empty))))))))
(.branch 3868 93221
(.branch 3797 83150
(.branch 3761 83270
(.branch 3743 83294
(.branch 3734 83173
(.branch 3730 82932
(.branch 3728 82934
(.branch 3727 83293
(.branch 3726 83220
.empty
.empty)
.empty)
(.branch 3729 83007
.empty
.empty))
(.branch 3732 83175
(.branch 3731 83005
.empty
.empty)
(.branch 3733 83150
.empty
.empty)))
(.branch 3739 83055
(.branch 3737 83053
(.branch 3736 83076
(.branch 3735 83148
.empty
.empty)
.empty)
(.branch 3738 83078
.empty
.empty))
(.branch 3741 83292
(.branch 3740 83221
.empty
.empty)
(.branch 3742 83223
.empty
.empty))))
(.branch 3752 83198
(.branch 3748 83172
(.branch 3746 82935
(.branch 3745 83004
(.branch 3744 82933
.empty
.empty)
.empty)
(.branch 3747 83006
.empty
.empty))
(.branch 3750 83174
(.branch 3749 83149
.empty
.empty)
(.branch 3751 83151
.empty
.empty)))
(.branch 3757 82982
(.branch 3755 83125
(.branch 3754 83196
(.branch 3753 83127
.empty
.empty)
.empty)
(.branch 3756 82959
.empty
.empty))
(.branch 3759 82980
(.branch 3758 82957
.empty
.empty)
(.branch 3760 83247
.empty
.empty)))))
(.branch 3779 83271
(.branch 3770 83199
(.branch 3766 83100
(.branch 3764 83102
(.branch 3763 83268
(.branch 3762 83245
.empty
.empty)
.empty)
(.branch 3765 83031
.empty
.empty))
(.branch 3768 83197
(.branch 3767 83029
.empty
.empty)
(.branch 3769 83124
.empty
.empty)))
(.branch 3775 82983
(.branch 3773 82981
(.branch 3772 82956
(.branch 3771 83126
.empty
.empty)
.empty)
(.branch 3774 82958
.empty
.empty))
(.branch 3777 83269
(.branch 3776 83244
.empty
.empty)
(.branch 3778 83246
.empty
.empty))))
(.branch 3788 83222
(.branch 3784 83079
(.branch 3782 83103
(.branch 3781 83028
(.branch 3780 83101
.empty
.empty)
.empty)
(.branch 3783 83030
.empty
.empty))
(.branch 3786 83077
(.branch 3785 83054
.empty
.empty)
(.branch 3787 83052
.empty
.empty)))
(.branch 3793 83007
(.branch 3791 83293
(.branch 3790 83220
(.branch 3789 83295
.empty
.empty)
.empty)
(.branch 3792 82934
.empty
.empty))
(.branch 3795 83005
(.branch 3794 82932
.empty
.empty)
(.branch 3796 83175
.empty
.empty))))))
(.branch 3833 93175
(.branch 3815 83151
(.branch 3806 83223
(.branch 3802 83078
(.branch 3800 83076
(.branch 3799 83148
(.branch 3798 83173
.empty
.empty)
.empty)
(.branch 3801 83053
.empty
.empty))
(.branch 3804 83221
(.branch 3803 83055
.empty
.empty)
(.branch 3805 83292
.empty
.empty)))
(.branch 3811 83006
(.branch 3809 83004
(.branch 3808 82933
(.branch 3807 83294
.empty
.empty)
.empty)
(.branch 3810 82935
.empty
.empty))
(.branch 3813 83149
(.branch 3812 83172
.empty
.empty)
(.branch 3814 83174
.empty
.empty))))
(.branch 3824 93199
(.branch 3820 92911
(.branch 3818 93076
(.branch 3817 93103
(.branch 3816 93127
.empty
.empty)
.empty)
(.branch 3819 93052
.empty
.empty))
(.branch 3822 93244
(.branch 3821 92935
.empty
.empty)
(.branch 3823 93268
.empty
.empty)))
(.branch 3829 93007
(.branch 3827 92980
(.branch 3826 92956
(.branch 3825 93223
.empty
.empty)
.empty)
(.branch 3828 93031
.empty
.empty))
(.branch 3831 93148
(.branch 3830 93172
.empty
.empty)
(.branch 3832 93151
.empty
.empty)))))
(.branch 3851 93102
(.branch 3842 92932
(.branch 3838 93220
(.branch 3836 92983
(.branch 3835 93028
(.branch 3834 93004
.empty
.empty)
.empty)
(.branch 3837 92959
.empty
.empty))
(.branch 3840 93271
(.branch 3839 93196
.empty
.empty)
(.branch 3841 93247
.empty
.empty)))
(.branch 3847 93124
(.branch 3845 93079
(.branch 3844 93055
(.branch 3843 92908
.empty
.empty)
.empty)
(.branch 3846 93100
.empty
.empty))
(.branch 3849 93053
(.branch 3848 93077
.empty
.empty)
(.branch 3850 93126
.empty
.empty))))
(.branch 3860 93173
(.branch 3856 92957
(.branch 3854 92910
(.branch 3853 93269
(.branch 3852 93245
.empty
.empty)
.empty)
(.branch 3855 92934
.empty
.empty))
(.branch 3858 93198
(.branch 3857 92981
.empty
.empty)
(.branch 3859 93222
.empty
.empty)))
(.branch 3864 93005
(.branch 3862 93030
(.branch 3861 93149
.empty
.empty)
(.branch 3863 93006
.empty
.empty))
(.branch 3866 93150
(.branch 3865 93029
.empty
.empty)
(.branch 3867 93174
.empty
.empty)))))))
(.branch 3940 93101
(.branch 3904 93271
(.branch 3886 93244
(.branch 3877 93125
(.branch 3873 92909
(.branch 3871 92958
(.branch 3870 92982
(.branch 3869 93197
.empty
.empty)
.empty)
(.branch 3872 92933
.empty
.empty))
(.branch 3875 93246
(.branch 3874 93270
.empty
.empty)
(.branch 3876 93101
.empty
.empty)))
(.branch 3882 93076
(.branch 3880 93127
(.branch 3879 93078
(.branch 3878 93054
.empty
.empty)
.empty)
(.branch 3881 93103
.empty
.empty))
(.branch 3884 92911
(.branch 3883 93052
.empty
.empty)
(.branch 3885 92935
.empty
.empty))))
(.branch 3895 93148
(.branch 3891 92980
(.branch 3889 93223
(.branch 3888 93199
(.branch 3887 93268
.empty
.empty)
.empty)
(.branch 3890 92956
.empty
.empty))
(.branch 3893 93007
(.branch 3892 93031
.empty
.empty)
(.branch 3894 93172
.empty
.empty)))
(.branch 3900 92983
(.branch 3898 93004
(.branch 3897 93175
(.branch 3896 93151
.empty
.empty)
.empty)
(.branch 3899 93028
.empty
.empty))
(.branch 3902 93220
(.branch 3901 92959
.empty
.empty)
(.branch 3903 93196
.empty
.empty)))))
(.branch 3922 93198
(.branch 3913 93053
(.branch 3909 93079
(.branch 3907 92908
(.branch 3906 92932
(.branch 3905 93247
.empty
.empty)
.empty)
(.branch 3908 93055
.empty
.empty))
(.branch 3911 93124
(.branch 3910 93100
.empty
.empty)
(.branch 3912 93077
.empty
.empty)))
(.branch 3918 92910
(.branch 3916 93245
(.branch 3915 93102
(.branch 3914 93126
.empty
.empty)
.empty)
(.branch 3917 93269
.empty
.empty))
(.branch 3920 92957
(.branch 3919 92934
.empty
.empty)
(.branch 3921 92981
.empty
.empty))))
(.branch 3931 93174
(.branch 3927 93006
(.branch 3925 93149
(.branch 3924 93173
(.branch 3923 93222
.empty
.empty)
.empty)
(.branch 3926 93030
.empty
.empty))
(.branch 3929 93029
(.branch 3928 93005
.empty
.empty)
(.branch 3930 93150
.empty
.empty)))
(.branch 3936 92933
(.branch 3934 92982
(.branch 3933 93197
(.branch 3932 93221
.empty
.empty)
.empty)
(.branch 3935 92958
.empty
.empty))
(.branch 3938 93270
(.branch 3937 92909
.empty
.empty)
(.branch 3939 93246
.empty
.empty))))))
(.branch 3976 78966
(.branch 3958 79037
(.branch 3949 78751
(.branch 3945 78988
(.branch 3943 93078
(.branch 3942 93054
(.branch 3941 93125
.empty
.empty)
.empty)
(.branch 3944 78967
.empty
.empty))
(.branch 3947 78871
(.branch 3946 78700
.empty
.empty)
(.branch 3948 78820
.empty
.empty)))
(.branch 3954 78702
(.branch 3952 78965
(.branch 3951 78916
(.branch 3950 79039
.empty
.empty)
.empty)
(.branch 3953 78990
.empty
.empty))
(.branch 3956 78822
(.branch 3955 78869
.empty
.empty)
(.branch 3957 78749
.empty
.empty))))
(.branch 3967 78799
(.branch 3963 78940
(.branch 3961 78727
(.branch 3960 78844
(.branch 3959 78918
.empty
.empty)
.empty)
(.branch 3962 79015
.empty
.empty))
(.branch 3965 79060
(.branch 3964 78895
.empty
.empty)
(.branch 3966 78772
.empty
.empty)))
(.branch 3972 78893
(.branch 3970 79013
(.branch 3969 78725
(.branch 3968 78846
.empty
.empty)
.empty)
(.branch 3971 78942
.empty
.empty))
(.branch 3974 78774
(.branch 3973 79062
.empty
.empty)
(.branch 3975 78797
.empty
.empty)))))
(.branch 3994 79014
(.branch 3985 78991
(.branch 3981 78750
(.branch 3979 78870
(.branch 3978 78701
(.branch 3977 78989
.empty
.empty)
.empty)
(.branch 3980 78821
.empty
.empty))
(.branch 3983 78917
(.branch 3982 79038
.empty
.empty)
(.branch 3984 78964
.empty
.empty)))
(.branch 3990 79036
(.branch 3988 78823
(.branch 3987 78868
(.branch 3986 78703
.empty
.empty)
.empty)
(.branch 3989 78748
.empty
.empty))
(.branch 3992 78845
(.branch 3991 78919
.empty
.empty)
(.branch 3993 78726
.empty
.empty))))
(.branch 4003 78943
(.branch 3999 78798
(.branch 3997 79061
(.branch 3996 78894
(.branch 3995 78941
.empty
.empty)
.empty)
(.branch 3998 78773
.empty
.empty))
(.branch 4001 78724
(.branch 4000 78847
.empty
.empty)
(.branch 4002 79012
.empty
.empty)))
(.branch 4007 78796
(.branch 4005 79063
(.branch 4004 78892
.empty
.empty)
(.branch 4006 78775
.empty
.empty))
(.branch 4009 78988
(.branch 4008 78967
.empty
.empty)
(.branch 4010 78700
.empty
.empty)))))))))
(.branch 4298 93087
(.branch 4155 78901
(.branch 4083 79021
(.branch 4047 78917
(.branch 4029 79060
(.branch 4020 78822
(.branch 4016 78965
(.branch 4014 79039
(.branch 4013 78751
(.branch 4012 78820
.empty
.empty)
.empty)
(.branch 4015 78916
.empty
.empty))
(.branch 4018 78702
(.branch 4017 78990
.empty
.empty)
(.branch 4019 78869
.empty
.empty)))
(.branch 4025 78727
(.branch 4023 78918
(.branch 4022 79037
(.branch 4021 78749
.empty
.empty)
.empty)
(.branch 4024 78844
.empty
.empty))
(.branch 4027 78940
(.branch 4026 79015
.empty
.empty)
(.branch 4028 78895
.empty
.empty))))
(.branch 4038 78774
(.branch 4034 79013
(.branch 4032 78846
(.branch 4031 78799
(.branch 4030 78772
.empty
.empty)
.empty)
(.branch 4033 78725
.empty
.empty))
(.branch 4036 78893
(.branch 4035 78942
.empty
.empty)
(.branch 4037 79062
.empty
.empty)))
(.branch 4043 78870
(.branch 4041 78989
(.branch 4040 78966
(.branch 4039 78797
.empty
.empty)
.empty)
(.branch 4042 78701
.empty
.empty))
(.branch 4045 78750
(.branch 4044 78821
.empty
.empty)
(.branch 4046 79038
.empty
.empty)))))
(.branch 4065 78724
(.branch 4056 78845
(.branch 4052 78823
(.branch 4050 78703
(.branch 4049 78991
(.branch 4048 78964
.empty
.empty)
.empty)
(.branch 4051 78868
.empty
.empty))
(.branch 4054 79036
(.branch 4053 78748
.empty
.empty)
(.branch 4055 78919
.empty
.empty)))
(.branch 4061 79061
(.branch 4059 78941
(.branch 4058 79014
(.branch 4057 78726
.empty
.empty)
.empty)
(.branch 4060 78894
.empty
.empty))
(.branch 4063 78798
(.branch 4062 78773
.empty
.empty)
(.branch 4064 78847
.empty
.empty))))
(.branch 4074 78853
(.branch 4070 78775
(.branch 4068 78892
(.branch 4067 78943
(.branch 4066 79012
.empty
.empty)
.empty)
(.branch 4069 79063
.empty
.empty))
(.branch 4072 78854
(.branch 4071 78796
.empty
.empty)
(.branch 4073 78975
.empty
.empty)))
(.branch 4079 78733
(.branch 4077 78734
(.branch 4076 78999
(.branch 4075 78972
.empty
.empty)
.empty)
(.branch 4078 78996
.empty
.empty))
(.branch 4081 79022
(.branch 4080 78711
.empty
.empty)
(.branch 4082 78708
.empty
.empty))))))
(.branch 4119 78878
(.branch 4101 78806
(.branch 4092 79070
(.branch 4088 78831
(.branch 4086 78949
(.branch 4085 78879
(.branch 4084 78950
.empty
.empty)
.empty)
(.branch 4087 78876
.empty
.empty))
(.branch 4090 78828
(.branch 4089 78902
.empty
.empty)
(.branch 4091 78901
.empty
.empty)))
(.branch 4097 79047
(.branch 4095 78756
(.branch 4094 79069
(.branch 4093 78759
.empty
.empty)
.empty)
(.branch 4096 78782
.empty
.empty))
(.branch 4099 79044
(.branch 4098 78781
.empty
.empty)
(.branch 4100 78927
.empty
.empty))))
(.branch 4110 78998
(.branch 4106 78855
(.branch 4104 78852
(.branch 4103 78805
(.branch 4102 78924
.empty
.empty)
.empty)
(.branch 4105 78973
.empty
.empty))
(.branch 4108 78997
(.branch 4107 78974
.empty
.empty)
(.branch 4109 78732
.empty
.empty)))
(.branch 4115 79023
(.branch 4113 79020
(.branch 4112 78709
(.branch 4111 78735
.empty
.empty)
.empty)
(.branch 4114 78710
.empty
.empty))
(.branch 4117 78877
(.branch 4116 78948
.empty
.empty)
(.branch 4118 78951
.empty
.empty)))))
(.branch 4137 78975
(.branch 4128 78780
(.branch 4124 79068
(.branch 4122 78830
(.branch 4121 78900
(.branch 4120 78829
.empty
.empty)
.empty)
(.branch 4123 78903
.empty
.empty))
(.branch 4126 79071
(.branch 4125 78757
.empty
.empty)
(.branch 4127 78758
.empty
.empty)))
(.branch 4133 78804
(.branch 4131 79046
(.branch 4130 78783
(.branch 4129 79045
.empty
.empty)
.empty)
(.branch 4132 78925
.empty
.empty))
(.branch 4135 78807
(.branch 4134 78926
.empty
.empty)
(.branch 4136 78854
.empty
.empty))))
(.branch 4146 78708
(.branch 4142 78996
(.branch 4140 78999
(.branch 4139 78972
(.branch 4138 78853
.empty
.empty)
.empty)
(.branch 4141 78734
.empty
.empty))
(.branch 4144 78711
(.branch 4143 78733
.empty
.empty)
(.branch 4145 79022
.empty
.empty)))
(.branch 4151 78876
(.branch 4149 78879
(.branch 4148 78950
(.branch 4147 79021
.empty
.empty)
.empty)
(.branch 4150 78949
.empty
.empty))
(.branch 4153 78902
(.branch 4152 78831
.empty
.empty)
(.branch 4154 78828
.empty
.empty)))))))
(.branch 4227 92916
(.branch 4191 78758
(.branch 4173 78732
(.branch 4164 78927
(.branch 4160 78782
(.branch 4158 79069
(.branch 4157 78759
(.branch 4156 79070
.empty
.empty)
.empty)
(.branch 4159 78756
.empty
.empty))
(.branch 4162 78781
(.branch 4161 79047
.empty
.empty)
(.branch 4163 79044
.empty
.empty)))
(.branch 4169 78973
(.branch 4167 78805
(.branch 4166 78924
(.branch 4165 78806
.empty
.empty)
.empty)
(.branch 4168 78852
.empty
.empty))
(.branch 4171 78974
(.branch 4170 78855
.empty
.empty)
(.branch 4172 78997
.empty
.empty))))
(.branch 4182 78951
(.branch 4178 78710
(.branch 4176 78709
(.branch 4175 78735
(.branch 4174 78998
.empty
.empty)
.empty)
(.branch 4177 79020
.empty
.empty))
(.branch 4180 78948
(.branch 4179 79023
.empty
.empty)
(.branch 4181 78877
.empty
.empty)))
(.branch 4187 78903
(.branch 4185 78900
(.branch 4184 78829
(.branch 4183 78878
.empty
.empty)
.empty)
(.branch 4186 78830
.empty
.empty))
(.branch 4189 78757
(.branch 4188 79068
.empty
.empty)
(.branch 4190 79071
.empty
.empty)))))
(.branch 4209 92918
(.branch 4200 93014
(.branch 4196 78925
(.branch 4194 78783
(.branch 4193 79045
(.branch 4192 78780
.empty
.empty)
.empty)
(.branch 4195 79046
.empty
.empty))
(.branch 4198 78926
(.branch 4197 78804
.empty
.empty)
(.branch 4199 78807
.empty
.empty)))
(.branch 4205 93206
(.branch 4203 93063
(.branch 4202 93135
(.branch 4201 93182
.empty
.empty)
.empty)
(.branch 4204 92990
.empty
.empty))
(.branch 4207 92943
(.branch 4206 93255
.empty
.empty)
(.branch 4208 93278
.empty
.empty))))
(.branch 4218 93012
(.branch 4214 93039
(.branch 4212 93110
(.branch 4211 93231
(.branch 4210 92967
.empty
.empty)
.empty)
(.branch 4213 93086
.empty
.empty))
(.branch 4216 93133
(.branch 4215 93159
.empty
.empty)
(.branch 4217 93061
.empty
.empty)))
(.branch 4223 93204
(.branch 4221 92941
(.branch 4220 93253
(.branch 4219 93180
.empty
.empty)
.empty)
(.branch 4222 92988
.empty
.empty))
(.branch 4225 93229
(.branch 4224 92965
.empty
.empty)
(.branch 4226 93276
.empty
.empty))))))
(.branch 4263 93132
(.branch 4245 93134
(.branch 4236 93230
(.branch 4232 93158
(.branch 4230 93108
(.branch 4229 93157
(.branch 4228 93037
.empty
.empty)
.empty)
(.branch 4231 93084
.empty
.empty))
(.branch 4234 93087
(.branch 4233 93038
.empty
.empty)
(.branch 4235 93111
.empty
.empty)))
(.branch 4241 93254
(.branch 4239 93279
(.branch 4238 92919
(.branch 4237 92966
.empty
.empty)
.empty)
(.branch 4240 92942
.empty
.empty))
(.branch 4243 92991
(.branch 4242 93207
.empty
.empty)
(.branch 4244 93062
.empty
.empty))))
(.branch 4254 93228
(.branch 4250 93156
(.branch 4248 93085
(.branch 4247 93015
(.branch 4246 93183
.empty
.empty)
.empty)
(.branch 4249 93109
.empty
.empty))
(.branch 4252 92917
(.branch 4251 93036
.empty
.empty)
(.branch 4253 93277
.empty
.empty)))
(.branch 4259 93252
(.branch 4257 92989
(.branch 4256 93205
(.branch 4255 92964
.empty
.empty)
.empty)
(.branch 4258 92940
.empty
.empty))
(.branch 4261 93013
(.branch 4260 93181
.empty
.empty)
(.branch 4262 93060
.empty
.empty)))))
(.branch 4281 93061
(.branch 4272 93278
(.branch 4268 92990
(.branch 4266 93135
(.branch 4265 93182
(.branch 4264 93014
.empty
.empty)
.empty)
(.branch 4267 93063
.empty
.empty))
(.branch 4270 93255
(.branch 4269 93206
.empty
.empty)
(.branch 4271 92943
.empty
.empty)))
(.branch 4277 93086
(.branch 4275 93231
(.branch 4274 92967
(.branch 4273 92918
.empty
.empty)
.empty)
(.branch 4276 93110
.empty
.empty))
(.branch 4279 93159
(.branch 4278 93039
.empty
.empty)
(.branch 4280 93133
.empty
.empty))))
(.branch 4290 93276
(.branch 4286 92988
(.branch 4284 93253
(.branch 4283 93180
(.branch 4282 93012
.empty
.empty)
.empty)
(.branch 4285 92941
.empty
.empty))
(.branch 4288 92965
(.branch 4287 93204
.empty
.empty)
(.branch 4289 93229
.empty
.empty)))
(.branch 4294 93108
(.branch 4292 93037
(.branch 4291 92916
.empty
.empty)
(.branch 4293 93157
.empty
.empty))
(.branch 4296 93158
(.branch 4295 93084
.empty
.empty)
(.branch 4297 93038
.empty
.empty))))))))
(.branch 4441 83094
(.branch 4370 83239
(.branch 4334 82950
(.branch 4316 92917
(.branch 4307 92991
(.branch 4303 93279
(.branch 4301 92966
(.branch 4300 93230
(.branch 4299 93111
.empty
.empty)
.empty)
(.branch 4302 92919
.empty
.empty))
(.branch 4305 93254
(.branch 4304 92942
.empty
.empty)
(.branch 4306 93207
.empty
.empty)))
(.branch 4312 93085
(.branch 4310 93183
(.branch 4309 93134
(.branch 4308 93062
.empty
.empty)
.empty)
(.branch 4311 93015
.empty
.empty))
(.branch 4314 93156
(.branch 4313 93109
.empty
.empty)
(.branch 4315 93036
.empty
.empty))))
(.branch 4325 93013
(.branch 4321 92989
(.branch 4319 92964
(.branch 4318 93228
(.branch 4317 93277
.empty
.empty)
.empty)
(.branch 4320 93205
.empty
.empty))
(.branch 4323 93252
(.branch 4322 92940
.empty
.empty)
(.branch 4324 93181
.empty
.empty)))
(.branch 4330 83068
(.branch 4328 83071
(.branch 4327 93132
(.branch 4326 93060
.empty
.empty)
.empty)
(.branch 4329 83117
.empty
.empty))
(.branch 4332 82949
(.branch 4331 83118
.empty
.empty)
(.branch 4333 83287
.empty
.empty)))))
(.branch 4352 82975
(.branch 4343 83022
(.branch 4339 82996
(.branch 4337 82999
(.branch 4336 83237
(.branch 4335 83284
.empty
.empty)
.empty)
(.branch 4338 83238
.empty
.empty))
(.branch 4341 83021
(.branch 4340 83167
.empty
.empty)
(.branch 4342 83164
.empty
.empty)))
(.branch 4348 83263
(.branch 4346 83142
(.branch 4345 83095
(.branch 4344 83141
.empty
.empty)
.empty)
(.branch 4347 83092
.empty
.empty))
(.branch 4350 83260
(.branch 4349 82925
.empty
.empty)
(.branch 4351 82926
.empty
.empty))))
(.branch 4361 83116
(.branch 4357 83191
(.branch 4355 83214
(.branch 4354 82972
(.branch 4353 83213
.empty
.empty)
.empty)
(.branch 4356 83045
.empty
.empty))
(.branch 4359 83188
(.branch 4358 83046
.empty
.empty)
(.branch 4360 83070
.empty
.empty)))
(.branch 4366 82951
(.branch 4364 82948
(.branch 4363 83119
(.branch 4362 83069
.empty
.empty)
.empty)
(.branch 4365 83286
.empty
.empty))
(.branch 4368 83236
(.branch 4367 83285
.empty
.empty)
(.branch 4369 82998
.empty
.empty))))))
(.branch 4406 83164
(.branch 4388 83044
(.branch 4379 83093
(.branch 4375 83023
(.branch 4373 83020
(.branch 4372 83166
(.branch 4371 82997
.empty
.empty)
.empty)
(.branch 4374 83165
.empty
.empty))
(.branch 4377 83094
(.branch 4376 83140
.empty
.empty)
(.branch 4378 83143
.empty
.empty)))
(.branch 4384 82974
(.branch 4382 83261
(.branch 4381 82924
(.branch 4380 83262
.empty
.empty)
.empty)
(.branch 4383 82927
.empty
.empty))
(.branch 4386 82973
(.branch 4385 83212
.empty
.empty)
(.branch 4387 83215
.empty
.empty))))
(.branch 4397 83287
(.branch 4393 83117
(.branch 4391 83189
(.branch 4390 83047
(.branch 4389 83190
.empty
.empty)
.empty)
(.branch 4392 83071
.empty
.empty))
(.branch 4395 83118
(.branch 4394 83068
.empty
.empty)
(.branch 4396 82949
.empty
.empty)))
(.branch 4402 83238
(.branch 4400 83237
(.branch 4399 83284
(.branch 4398 82950
.empty
.empty)
.empty)
(.branch 4401 82999
.empty
.empty))
(.branch 4404 83167
(.branch 4403 82996
.empty
.empty)
(.branch 4405 83021
.empty
.empty)))))
(.branch 4424 83070
(.branch 4415 82926
(.branch 4411 83092
(.branch 4409 83095
(.branch 4408 83141
(.branch 4407 83022
.empty
.empty)
.empty)
(.branch 4410 83142
.empty
.empty))
(.branch 4413 82925
(.branch 4412 83263
.empty
.empty)
(.branch 4414 83260
.empty
.empty)))
(.branch 4420 83045
(.branch 4418 82972
(.branch 4417 83213
(.branch 4416 82975
.empty
.empty)
.empty)
(.branch 4419 83214
.empty
.empty))
(.branch 4422 83046
(.branch 4421 83191
.empty
.empty)
(.branch 4423 83188
.empty
.empty))))
(.branch 4433 82998
(.branch 4429 83286
(.branch 4427 83119
(.branch 4426 83069
(.branch 4425 83116
.empty
.empty)
.empty)
(.branch 4428 82948
.empty
.empty))
(.branch 4431 83285
(.branch 4430 82951
.empty
.empty)
(.branch 4432 83236
.empty
.empty)))
(.branch 4437 83020
(.branch 4435 82997
(.branch 4434 83239
.empty
.empty)
(.branch 4436 83166
.empty
.empty))
(.branch 4439 83023
(.branch 4438 83165
.empty
.empty)
(.branch 4440 83140
.empty
.empty)))))))
(.branch 4513 88686
(.branch 4477 88972
(.branch 4459 88901
(.branch 4450 82973
(.branch 4446 83261
(.branch 4444 83262
(.branch 4443 83093
(.branch 4442 83143
.empty
.empty)
.empty)
(.branch 4445 82924
.empty
.empty))
(.branch 4448 82974
(.branch 4447 82927
.empty
.empty)
(.branch 4449 83212
.empty
.empty)))
(.branch 4455 83189
(.branch 4453 83190
(.branch 4452 83044
(.branch 4451 83215
.empty
.empty)
.empty)
(.branch 4454 83047
.empty
.empty))
(.branch 4457 88780
(.branch 4456 88783
.empty
.empty)
(.branch 4458 88902
.empty
.empty))))
(.branch 4468 88879
(.branch 4464 89046
(.branch 4462 89023
(.branch 4461 88757
(.branch 4460 88758
.empty
.empty)
.empty)
(.branch 4463 89020
.empty
.empty))
(.branch 4466 88735
(.branch 4465 89045
.empty
.empty)
(.branch 4467 88732
.empty
.empty)))
(.branch 4473 88949
(.branch 4471 88805
(.branch 4470 88806
(.branch 4469 88876
.empty
.empty)
.empty)
(.branch 4472 88950
.empty
.empty))
(.branch 4475 88828
(.branch 4474 88831
.empty
.empty)
(.branch 4476 88975
.empty
.empty)))))
(.branch 4495 89022
(.branch 4486 88927
(.branch 4482 88998
(.branch 4480 88687
(.branch 4479 88709
(.branch 4478 88710
.empty
.empty)
.empty)
(.branch 4481 88684
.empty
.empty))
(.branch 4484 88854
(.branch 4483 88997
.empty
.empty)
(.branch 4485 88853
.empty
.empty)))
(.branch 4491 88903
(.branch 4489 88782
(.branch 4488 88781
(.branch 4487 88924
.empty
.empty)
.empty)
(.branch 4490 88900
.empty
.empty))
(.branch 4493 88759
(.branch 4492 88756
.empty
.empty)
(.branch 4494 89021
.empty
.empty))))
(.branch 4504 88948
(.branch 4500 88877
(.branch 4498 88733
(.branch 4497 89047
(.branch 4496 89044
.empty
.empty)
.empty)
(.branch 4499 88734
.empty
.empty))
(.branch 4502 88804
(.branch 4501 88878
.empty
.empty)
(.branch 4503 88807
.empty
.empty)))
(.branch 4509 88974
(.branch 4507 88830
(.branch 4506 88829
(.branch 4505 88951
.empty
.empty)
.empty)
(.branch 4508 88973
.empty
.empty))
(.branch 4511 88711
(.branch 4510 88708
.empty
.empty)
(.branch 4512 88685
.empty
.empty))))))
(.branch 4549 88853
(.branch 4531 88732
(.branch 4522 88902
(.branch 4518 88925
(.branch 4516 88852
(.branch 4515 88999
(.branch 4514 88996
.empty
.empty)
.empty)
(.branch 4517 88855
.empty
.empty))
(.branch 4520 88783
(.branch 4519 88926
.empty
.empty)
(.branch 4521 88780
.empty
.empty)))
(.branch 4527 89020
(.branch 4525 88757
(.branch 4524 88758
(.branch 4523 88901
.empty
.empty)
.empty)
(.branch 4526 89023
.empty
.empty))
(.branch 4529 89045
(.branch 4528 89046
.empty
.empty)
(.branch 4530 88735
.empty
.empty))))
(.branch 4540 88975
(.branch 4536 88950
(.branch 4534 88806
(.branch 4533 88876
(.branch 4532 88879
.empty
.empty)
.empty)
(.branch 4535 88805
.empty
.empty))
(.branch 4538 88831
(.branch 4537 88949
.empty
.empty)
(.branch 4539 88828
.empty
.empty)))
(.branch 4545 88684
(.branch 4543 88709
(.branch 4542 88710
(.branch 4541 88972
.empty
.empty)
.empty)
(.branch 4544 88687
.empty
.empty))
(.branch 4547 88997
(.branch 4546 88998
.empty
.empty)
(.branch 4548 88854
.empty
.empty)))))
(.branch 4567 88807
(.branch 4558 89021
(.branch 4554 88900
(.branch 4552 88781
(.branch 4551 88924
(.branch 4550 88927
.empty
.empty)
.empty)
(.branch 4553 88782
.empty
.empty))
(.branch 4556 88756
(.branch 4555 88903
.empty
.empty)
(.branch 4557 88759
.empty
.empty)))
(.branch 4563 88734
(.branch 4561 89047
(.branch 4560 89044
(.branch 4559 89022
.empty
.empty)
.empty)
(.branch 4562 88733
.empty
.empty))
(.branch 4565 88878
(.branch 4564 88877
.empty
.empty)
(.branch 4566 88804
.empty
.empty))))
(.branch 4576 88685
(.branch 4572 88973
(.branch 4570 88829
(.branch 4569 88951
(.branch 4568 88948
.empty
.empty)
.empty)
(.branch 4571 88830
.empty
.empty))
(.branch 4574 88708
(.branch 4573 88974
.empty
.empty)
(.branch 4575 88711
.empty
.empty)))
(.branch 4580 88852
(.branch 4578 88996
(.branch 4577 88686
.empty
.empty)
(.branch 4579 88999
.empty
.empty))
(.branch 4582 88925
(.branch 4581 88855
.empty
.empty)
(.branch 4583 88926
.empty
.empty))))))))))))

/-- Bounded lookup of the complete candidate original source labels for frame 3. -/
def generatedAxisGlobalOddFourthSelectedSourceTree03 : GeneratedAxisGlobalSparseLookupTree (Fin 98280) :=
  (.branch 2292 390
(.branch 1146 37860
(.branch 573 529
(.branch 286 33070
(.branch 143 1016
(.branch 71 743
(.branch 35 600
(.branch 17 1
(.branch 8 33118
(.branch 4 33105
(.branch 2 33006
(.branch 1 33233
(.branch 0 32942
.empty
.empty)
.empty)
(.branch 3 33134
.empty
.empty))
(.branch 6 33150
(.branch 5 33182
.empty
.empty)
(.branch 7 33169
.empty
.empty)))
(.branch 13 33057
(.branch 11 32990
(.branch 10 33073
(.branch 9 33089
.empty
.empty)
.empty)
(.branch 12 45
.empty
.empty))
(.branch 15 33022
(.branch 14 33217
.empty
.empty)
(.branch 16 32958
.empty
.empty))))
(.branch 26 648
(.branch 22 299
(.branch 20 32977
(.branch 19 33198
(.branch 18 33249
.empty
.empty)
.empty)
(.branch 21 33038
.empty
.empty))
(.branch 24 567
(.branch 23 1134
.empty
.empty)
(.branch 25 823
.empty
.empty)))
(.branch 31 632
(.branch 29 840
(.branch 28 839
(.branch 27 871
.empty
.empty)
.empty)
(.branch 30 679
.empty
.empty))
(.branch 33 432
(.branch 32 616
.empty
.empty)
(.branch 34 32946
.empty
.empty)))))
(.branch 53 945
(.branch 44 32936
(.branch 40 1131
(.branch 38 433
(.branch 37 583
(.branch 36 1133
.empty
.empty)
.empty)
(.branch 39 32939
.empty
.empty))
(.branch 42 434
(.branch 41 1143
.empty
.empty)
(.branch 43 599
.empty
.empty)))
(.branch 49 766
(.branch 47 977
(.branch 46 750
(.branch 45 1070
.empty
.empty)
.empty)
(.branch 48 798
.empty
.empty))
(.branch 51 990
(.branch 50 785
.empty
.empty)
(.branch 52 961
.empty
.empty))))
(.branch 62 364
(.branch 58 1086
(.branch 56 1121
(.branch 55 33229
(.branch 54 1182
.empty
.empty)
.empty)
(.branch 57 86
.empty
.empty))
(.branch 60 33236
(.branch 59 1150
.empty
.empty)
(.branch 61 87
.empty
.empty)))
(.branch 67 712
(.branch 65 33239
(.branch 64 1102
(.branch 63 1169
.empty
.empty)
.empty)
(.branch 66 887
.empty
.empty))
(.branch 69 903
(.branch 68 935
.empty
.empty)
(.branch 70 904
.empty
.empty))))))
(.branch 107 1041
(.branch 89 548
(.branch 80 33003
(.branch 76 507
(.branch 74 564
(.branch 73 680
(.branch 72 696
.empty
.empty)
.empty)
(.branch 75 33010
.empty
.empty))
(.branch 78 487
(.branch 77 1069
.empty
.empty)
(.branch 79 562
.empty
.empty)))
(.branch 85 33000
(.branch 83 558
(.branch 82 1079
(.branch 81 1067
.empty
.empty)
.empty)
(.branch 84 497
.empty
.empty))
(.branch 87 546
(.branch 86 1006
.empty
.empty)
(.branch 88 547
.empty
.empty))))
(.branch 98 818
(.branch 94 33138
(.branch 92 1000
(.branch 91 1005
(.branch 90 1012
.empty
.empty)
.empty)
(.branch 93 820
.empty
.empty))
(.branch 96 749
(.branch 95 875
.empty
.empty)
(.branch 97 882
.empty
.empty)))
(.branch 103 881
(.branch 101 759
(.branch 100 747
(.branch 99 33131
.empty
.empty)
.empty)
(.branch 102 814
.empty
.empty))
(.branch 105 1054
(.branch 104 33128
.empty
.empty)
(.branch 106 1022
.empty
.empty)))))
(.branch 125 1060
(.branch 116 653
(.branch 112 33101
(.branch 110 531
(.branch 109 248
(.branch 108 256
.empty
.empty)
.empty)
(.branch 111 651
.empty
.empty))
(.branch 114 978
(.branch 113 724
.empty
.empty)
(.branch 115 717
.empty
.empty)))
(.branch 121 718
(.branch 119 968
(.branch 118 980
(.branch 117 33108
.empty
.empty)
.empty)
(.branch 120 657
.empty
.empty))
(.branch 123 273
(.branch 122 33111
.empty
.empty)
(.branch 124 274
.empty
.empty))))
(.branch 134 33179
(.branch 130 923
(.branch 128 868
(.branch 127 1048
(.branch 126 1053
.empty
.empty)
.empty)
(.branch 129 33186
.empty
.empty))
(.branch 132 930
(.branch 131 797
.empty
.empty)
(.branch 133 866
.empty
.empty)))
(.branch 139 33176
(.branch 137 862
(.branch 136 807
(.branch 135 795
.empty
.empty)
.empty)
(.branch 138 929
.empty
.empty))
(.branch 141 1028
(.branch 140 275
.empty
.empty)
(.branch 142 1021
.empty
.empty)))))))
(.branch 215 32987
(.branch 179 33115
(.branch 161 916
(.branch 152 775
(.branch 148 898
(.branch 146 891
(.branch 145 33154
(.branch 144 836
.empty
.empty)
.empty)
(.branch 147 765
.empty
.empty))
(.branch 150 33147
(.branch 149 834
.empty
.empty)
(.branch 151 763
.empty
.empty)))
(.branch 157 1042
(.branch 155 33144
(.branch 154 897
(.branch 153 830
.empty
.empty)
.empty)
(.branch 156 1035
.empty
.empty))
(.branch 159 843
(.branch 158 1047
.empty
.empty)
(.branch 160 33165
.empty
.empty))))
(.branch 170 33175
(.branch 166 788
(.branch 164 845
(.branch 163 909
(.branch 162 786
.empty
.empty)
.empty)
(.branch 165 33172
.empty
.empty))
(.branch 168 849
(.branch 167 776
.empty
.empty)
(.branch 169 910
.empty
.empty)))
(.branch 175 731
(.branch 173 676
(.branch 172 537
(.branch 171 250
.empty
.empty)
.empty)
(.branch 174 33122
.empty
.empty))
(.branch 177 738
(.branch 176 989
.empty
.empty)
(.branch 178 674
.empty
.empty)))))
(.branch 197 33095
(.branch 188 708
(.branch 184 33112
(.branch 182 670
(.branch 181 999
(.branch 180 987
.empty
.empty)
.empty)
(.branch 183 737
.empty
.empty))
(.branch 186 635
(.branch 185 525
.empty
.empty)
(.branch 187 33085
.empty
.empty)))
(.branch 193 964
(.branch 191 637
(.branch 190 701
(.branch 189 962
.empty
.empty)
.empty)
(.branch 192 33092
.empty
.empty))
(.branch 195 641
(.branch 194 952
.empty
.empty)
(.branch 196 702
.empty
.empty))))
(.branch 206 936
(.branch 202 685
(.branch 200 692
(.branch 199 33069
(.branch 198 619
.empty
.empty)
.empty)
(.branch 201 946
.empty
.empty))
(.branch 204 33076
(.branch 203 621
.empty
.empty)
(.branch 205 948
.empty
.empty)))
(.branch 211 603
(.branch 209 33079
(.branch 208 686
(.branch 207 625
.empty
.empty)
.empty)
(.branch 210 32994
.empty
.empty))
(.branch 213 580
(.branch 212 1181
.empty
.empty)
(.branch 214 171
.empty
.empty))))))
(.branch 251 1095
(.branch 233 605
(.branch 224 32962
(.branch 220 32984
(.branch 218 172
(.branch 217 1191
(.branch 216 1179
.empty
.empty)
.empty)
(.branch 219 596
.empty
.empty))
(.branch 222 33213
(.branch 221 33053
.empty
.empty)
(.branch 223 33026
.empty
.empty)))
(.branch 229 33042
(.branch 227 33202
(.branch 226 33245
(.branch 225 2
.empty
.empty)
.empty)
(.branch 228 32973
.empty
.empty))
(.branch 231 1122
(.branch 230 300
.empty
.empty)
(.branch 232 212
.empty
.empty))))
(.branch 242 33220
(.branch 238 222
(.branch 236 1112
(.branch 235 1124
(.branch 234 33060
.empty
.empty)
.empty)
(.branch 237 609
.empty
.empty))
(.branch 240 1085
(.branch 239 33063
.empty
.empty)
(.branch 241 1149
.empty
.empty)))
(.branch 247 33223
(.branch 245 1170
(.branch 244 382
(.branch 243 105
.empty
.empty)
.empty)
(.branch 246 1101
.empty
.empty))
(.branch 249 33019
(.branch 248 578
.empty
.empty)
(.branch 250 1083
.empty
.empty)))))
(.branch 269 33255
(.branch 260 32952
(.branch 256 1147
(.branch 254 33016
(.branch 253 210
(.branch 252 574
.empty
.empty)
.empty)
(.branch 255 32955
.empty
.empty))
(.branch 258 185
(.branch 257 1159
.empty
.empty)
(.branch 259 594
.empty
.empty)))
(.branch 265 276
(.branch 263 32980
(.branch 262 33195
(.branch 261 33252
.empty
.empty)
.empty)
(.branch 264 33035
.empty
.empty))
(.branch 267 1172
(.branch 266 399
.empty
.empty)
(.branch 268 1099
.empty
.empty))))
(.branch 278 33009
(.branch 274 32983
(.branch 272 33192
(.branch 271 1111
(.branch 270 1160
.empty
.empty)
.empty)
(.branch 273 590
.empty
.empty))
(.branch 276 32945
(.branch 275 33032
.empty
.empty)
(.branch 277 33230
.empty
.empty)))
(.branch 282 33153
(.branch 280 33102
(.branch 279 33137
.empty
.empty)
(.branch 281 33185
.empty
.empty))
(.branch 284 33121
(.branch 283 33166
.empty
.empty)
(.branch 285 33086
.empty
.empty))))))))
(.branch 430 894
(.branch 358 1064
(.branch 322 753
(.branch 304 824
(.branch 295 33201
(.branch 291 33025
(.branch 289 33054
(.branch 288 0
(.branch 287 32993
.empty
.empty)
.empty)
(.branch 290 33214
.empty
.empty))
(.branch 293 24
(.branch 292 32961
.empty
.empty)
(.branch 294 33246
.empty
.empty)))
(.branch 300 552
(.branch 298 278
(.branch 297 33041
(.branch 296 32974
.empty
.empty)
.empty)
(.branch 299 1137
.empty
.empty))
(.branch 302 663
(.branch 301 808
.empty
.empty)
(.branch 303 856
.empty
.empty))))
(.branch 313 568
(.branch 309 461
(.branch 307 647
(.branch 306 664
(.branch 305 855
.empty
.empty)
.empty)
(.branch 308 631
.empty
.empty))
(.branch 311 615
(.branch 310 32941
.empty
.empty)
(.branch 312 1138
.empty
.empty)))
(.branch 318 447
(.branch 316 1140
(.branch 315 32948
(.branch 314 448
.empty
.empty)
.empty)
(.branch 317 1128
.empty
.empty))
(.branch 320 32951
(.branch 319 584
.empty
.empty)
(.branch 321 1073
.empty
.empty)))))
(.branch 340 1105
(.branch 331 33234
(.branch 327 993
(.branch 325 769
(.branch 324 801
(.branch 323 974
.empty
.empty)
.empty)
(.branch 326 782
.empty
.empty))
(.branch 329 942
(.branch 328 958
.empty
.empty)
(.branch 330 1185
.empty
.empty)))
(.branch 336 33227
(.branch 334 1089
(.branch 333 123
(.branch 332 1118
.empty
.empty)
.empty)
(.branch 335 1153
.empty
.empty))
(.branch 338 381
(.branch 337 106
.empty
.empty)
(.branch 339 1166
.empty
.empty))))
(.branch 349 695
(.branch 345 888
(.branch 343 727
(.branch 342 872
(.branch 341 33224
.empty
.empty)
.empty)
(.branch 344 920
.empty
.empty))
(.branch 347 728
(.branch 346 919
.empty
.empty)
(.branch 348 711
.empty
.empty)))
(.branch 354 498
(.branch 352 486
(.branch 351 33005
(.branch 350 555
.empty
.empty)
.empty)
(.branch 353 1074
.empty
.empty))
(.branch 356 33012
(.branch 355 557
.empty
.empty)
(.branch 357 1076
.empty
.empty))))))
(.branch 394 971
(.branch 376 756
(.branch 367 1010
(.branch 363 551
(.branch 361 33015
(.branch 360 488
(.branch 359 561
.empty
.empty)
.empty)
(.branch 362 1009
.empty
.empty))
(.branch 365 549
(.branch 364 550
.empty
.empty)
(.branch 366 1003
.empty
.empty)))
(.branch 372 754
(.branch 370 33133
(.branch 369 811
(.branch 368 1015
.empty
.empty)
.empty)
(.branch 371 884
.empty
.empty))
(.branch 374 813
(.branch 373 877
.empty
.empty)
(.branch 375 33140
.empty
.empty))))
(.branch 385 261
(.branch 381 1057
(.branch 379 878
(.branch 378 817
(.branch 377 744
.empty
.empty)
.empty)
(.branch 380 33143
.empty
.empty))
(.branch 383 1038
(.branch 382 1025
.empty
.empty)
(.branch 384 249
.empty
.empty)))
(.branch 390 973
(.branch 388 33106
(.branch 387 660
(.branch 386 526
.empty
.empty)
.empty)
(.branch 389 715
.empty
.empty))
(.branch 392 658
(.branch 391 722
.empty
.empty)
(.branch 393 33099
.empty
.empty)))))
(.branch 412 792
(.branch 403 1063
(.branch 399 272
(.branch 397 721
(.branch 396 654
(.branch 395 983
.empty
.empty)
.empty)
(.branch 398 33096
.empty
.empty))
(.branch 401 1051
(.branch 400 271
.empty
.empty)
(.branch 402 1058
.empty
.empty)))
(.branch 408 925
(.branch 406 932
(.branch 405 33181
(.branch 404 859
.empty
.empty)
.empty)
(.branch 407 802
.empty
.empty))
(.branch 410 33188
(.branch 409 861
.empty
.empty)
(.branch 411 804
.empty
.empty))))
(.branch 421 33149
(.branch 417 1019
(.branch 415 33191
(.branch 414 926
(.branch 413 865
.empty
.empty)
.empty)
(.branch 416 270
.empty
.empty))
(.branch 419 1031
(.branch 418 1026
.empty
.empty)
(.branch 420 827
.empty
.empty)))
(.branch 426 33156
(.branch 424 893
(.branch 423 770
(.branch 422 900
.empty
.empty)
.empty)
(.branch 425 829
.empty
.empty))
(.branch 428 760
(.branch 427 772
.empty
.empty)
(.branch 429 833
.empty
.empty)))))))
(.branch 502 33250
(.branch 466 706
(.branch 448 524
(.branch 439 914
(.branch 435 852
(.branch 433 1037
(.branch 432 1044
(.branch 431 33159
.empty
.empty)
.empty)
(.branch 434 1032
.empty
.empty))
(.branch 437 907
(.branch 436 33170
.empty
.empty)
(.branch 438 781
.empty
.empty)))
(.branch 444 846
(.branch 442 779
(.branch 441 33163
(.branch 440 850
.empty
.empty)
.empty)
(.branch 443 791
.empty
.empty))
(.branch 446 33160
(.branch 445 913
.empty
.empty)
(.branch 447 255
.empty
.empty))))
(.branch 457 984
(.branch 453 733
(.branch 451 740
(.branch 450 33117
(.branch 449 667
.empty
.empty)
.empty)
(.branch 452 994
.empty
.empty))
(.branch 455 33124
(.branch 454 669
.empty
.empty)
(.branch 456 996
.empty
.empty)))
(.branch 462 644
(.branch 460 33127
(.branch 459 734
(.branch 458 673
.empty
.empty)
.empty)
(.branch 461 532
.empty
.empty))
(.branch 464 699
(.branch 463 33090
.empty
.empty)
(.branch 465 957
.empty
.empty)))))
(.branch 484 689
(.branch 475 33074
(.branch 471 638
(.branch 469 955
(.branch 468 33083
(.branch 467 642
.empty
.empty)
.empty)
(.branch 470 967
.empty
.empty))
(.branch 473 33080
(.branch 472 705
.empty
.empty)
(.branch 474 628
.empty
.empty)))
(.branch 480 33067
(.branch 478 690
(.branch 477 941
(.branch 476 683
.empty
.empty)
.empty)
(.branch 479 626
.empty
.empty))
(.branch 482 951
(.branch 481 939
.empty
.empty)
(.branch 483 622
.empty
.empty))))
(.branch 493 1176
(.branch 489 571
(.branch 487 612
(.branch 486 32989
(.branch 485 33064
.empty
.empty)
.empty)
(.branch 488 1186
.empty
.empty))
(.branch 491 32996
(.branch 490 158
.empty
.empty)
(.branch 492 1188
.empty
.empty)))
(.branch 498 33218
(.branch 496 32999
(.branch 495 587
(.branch 494 157
.empty
.empty)
.empty)
(.branch 497 33058
.empty
.empty))
(.branch 500 32957
(.branch 499 33021
.empty
.empty)
(.branch 501 23
.empty
.empty))))))
(.branch 538 33204
(.branch 520 363
(.branch 511 1115
(.branch 507 1117
(.branch 505 33037
(.branch 504 32978
(.branch 503 33197
.empty
.empty)
.empty)
(.branch 506 277
.empty
.empty))
(.branch 509 610
(.branch 508 221
.empty
.empty)
(.branch 510 33051
.empty
.empty)))
(.branch 516 1090
(.branch 514 211
(.branch 513 606
(.branch 512 1127
.empty
.empty)
.empty)
(.branch 515 33048
.empty
.empty))
(.branch 518 33211
(.branch 517 1154
.empty
.empty)
(.branch 519 88
.empty
.empty))))
(.branch 529 231
(.branch 525 33028
(.branch 523 33208
(.branch 522 1106
(.branch 521 1165
.empty
.empty)
.empty)
(.branch 524 573
.empty
.empty))
(.branch 527 1080
(.branch 526 1092
.empty
.empty)
(.branch 528 577
.empty
.empty)))
(.branch 534 156
(.branch 532 1156
(.branch 531 32964
(.branch 530 33031
.empty
.empty)
.empty)
(.branch 533 1144
.empty
.empty))
(.branch 536 32967
(.branch 535 589
.empty
.empty)
(.branch 537 33243
.empty
.empty)))))
(.branch 556 252
(.branch 547 1096
(.branch 543 1163
(.branch 541 321
(.branch 540 33044
(.branch 539 32971
.empty
.empty)
.empty)
(.branch 542 362
.empty
.empty))
(.branch 545 33240
(.branch 544 1108
.empty
.empty)
(.branch 546 1175
.empty
.empty)))
(.branch 552 1027
(.branch 550 32968
(.branch 549 593
(.branch 548 33207
.empty
.empty)
.empty)
(.branch 551 33047
.empty
.empty))
(.branch 554 1023
(.branch 553 527
.empty
.empty)
(.branch 555 533
.empty
.empty))))
(.branch 565 530
(.branch 561 1004
(.branch 559 1040
(.branch 558 258
(.branch 557 1036
.empty
.empty)
.empty)
(.branch 560 253
.empty
.empty))
(.branch 563 1008
(.branch 562 259
.empty
.empty)
(.branch 564 1052
.empty
.empty)))
(.branch 569 1059
(.branch 567 536
(.branch 566 1056
.empty
.empty)
(.branch 568 254
.empty
.empty))
(.branch 571 1055
(.branch 570 260
.empty
.empty)
(.branch 572 1011
.empty
.empty)))))))))
(.branch 860 10326
(.branch 717 37771
(.branch 645 37853
(.branch 609 543
(.branch 591 1033
(.branch 582 257
(.branch 578 1039
(.branch 576 1043
(.branch 575 535
(.branch 574 1007
.empty
.empty)
.empty)
(.branch 577 528
.empty
.empty))
(.branch 580 251
(.branch 579 534
.empty
.empty)
(.branch 581 1020
.empty
.empty)))
(.branch 587 538
(.branch 585 542
(.branch 584 1029
(.branch 583 1024
.empty
.empty)
.empty)
(.branch 586 1030
.empty
.empty))
(.branch 589 1034
(.branch 588 267
.empty
.empty)
(.branch 590 263
.empty
.empty))))
(.branch 600 269
(.branch 596 1050
(.branch 594 264
(.branch 593 1002
(.branch 592 268
.empty
.empty)
.empty)
(.branch 595 1001
.empty
.empty))
(.branch 598 1049
(.branch 597 545
.empty
.empty)
(.branch 599 541
.empty
.empty)))
(.branch 605 544
(.branch 603 1062
(.branch 602 265
(.branch 601 1061
.empty
.empty)
.empty)
(.branch 604 1013
.empty
.empty))
(.branch 607 540
(.branch 606 1014
.empty
.empty)
(.branch 608 1045
.empty
.empty)))))
(.branch 627 13294
(.branch 618 37665
(.branch 614 262
(.branch 612 266
(.branch 611 539
(.branch 610 1046
.empty
.empty)
.empty)
(.branch 613 1018
.empty
.empty))
(.branch 616 13234
(.branch 615 1017
.empty
.empty)
(.branch 617 13233
.empty
.empty)))
(.branch 623 13473
(.branch 621 37810
(.branch 620 37809
(.branch 619 37666
.empty
.empty)
.empty)
(.branch 622 13474
.empty
.empty))
(.branch 625 37725
(.branch 624 37726
.empty
.empty)
(.branch 626 13293
.empty
.empty))))
(.branch 636 13362
(.branch 632 37681
(.branch 630 37742
(.branch 629 13406
(.branch 628 13405
.empty
.empty)
.empty)
(.branch 631 37741
.empty
.empty))
(.branch 634 13346
(.branch 633 37682
.empty
.empty)
(.branch 635 13345
.empty
.empty)))
(.branch 641 13278
(.branch 639 37794
(.branch 638 37793
(.branch 637 13361
.empty
.empty)
.empty)
(.branch 640 13277
.empty
.empty))
(.branch 643 37613
(.branch 642 37614
.empty
.empty)
(.branch 644 37854
.empty
.empty))))))
(.branch 681 37828
(.branch 663 13358
(.branch 654 37857
(.branch 650 13282
(.branch 648 37617
(.branch 647 13422
(.branch 646 13421
.empty
.empty)
.empty)
(.branch 649 37618
.empty
.empty))
(.branch 652 13426
(.branch 651 13281
.empty
.empty)
(.branch 653 13425
.empty
.empty)))
(.branch 659 37677
(.branch 657 13342
(.branch 656 13341
(.branch 655 37858
.empty
.empty)
.empty)
(.branch 658 37678
.empty
.empty))
(.branch 661 37789
(.branch 660 37790
.empty
.empty)
(.branch 662 13357
.empty
.empty))))
(.branch 672 37662
(.branch 668 37745
(.branch 666 37729
(.branch 665 13297
(.branch 664 13298
.empty
.empty)
.empty)
(.branch 667 37730
.empty
.empty))
(.branch 670 13410
(.branch 669 37746
.empty
.empty)
(.branch 671 13409
.empty
.empty)))
(.branch 677 13470
(.branch 675 13230
(.branch 674 13229
(.branch 673 37661
.empty
.empty)
.empty)
(.branch 676 13469
.empty
.empty))
(.branch 679 37805
(.branch 678 37806
.empty
.empty)
(.branch 680 37780
.empty
.empty)))))
(.branch 699 13240
(.branch 690 13332
(.branch 686 13435
(.branch 684 37755
(.branch 683 13380
(.branch 682 13460
.empty
.empty)
.empty)
(.branch 685 37835
.empty
.empty))
(.branch 688 37652
(.branch 687 13387
.empty
.empty)
(.branch 689 37700
.empty
.empty)))
(.branch 695 13259
(.branch 693 37707
(.branch 692 37627
(.branch 691 13252
.empty
.empty)
.empty)
(.branch 694 13307
.empty
.empty))
(.branch 697 37688
(.branch 696 37640
.empty
.empty)
(.branch 698 13320
.empty
.empty))))
(.branch 708 37767
(.branch 704 37768
(.branch 702 13319
(.branch 701 37719
(.branch 700 37639
.empty
.empty)
.empty)
(.branch 703 13271
.empty
.empty))
(.branch 706 13448
(.branch 705 37816
.empty
.empty)
(.branch 707 13368
.empty
.empty)))
(.branch 713 37764
(.branch 711 13399
(.branch 710 13447
(.branch 709 37847
.empty
.empty)
.empty)
(.branch 712 37844
.empty
.empty))
(.branch 715 13444
(.branch 714 13396
.empty
.empty)
(.branch 716 37819
.empty
.empty)))))))
(.branch 789 34783
(.branch 753 10399
(.branch 735 13335
(.branch 726 13243
(.branch 722 13268
(.branch 720 37716
(.branch 719 13451
(.branch 718 13371
.empty
.empty)
.empty)
(.branch 721 37636
.empty
.empty))
(.branch 724 37691
(.branch 723 13316
.empty
.empty)
(.branch 725 37643
.empty
.empty)))
(.branch 731 13304
(.branch 729 37624
(.branch 728 37704
(.branch 727 13323
.empty
.empty)
.empty)
(.branch 730 13256
.empty
.empty))
(.branch 733 37655
(.branch 732 37703
.empty
.empty)
(.branch 734 13255
.empty
.empty))))
(.branch 744 10163
(.branch 740 37831
(.branch 738 13384
(.branch 737 37752
(.branch 736 37832
.empty
.empty)
.empty)
(.branch 739 13432
.empty
.empty))
(.branch 742 13383
(.branch 741 37783
.empty
.empty)
(.branch 743 13463
.empty
.empty)))
(.branch 749 10211
(.branch 747 10403
(.branch 746 10291
(.branch 745 10275
.empty
.empty)
.empty)
(.branch 748 10227
.empty
.empty))
(.branch 751 10339
(.branch 750 10355
.empty
.empty)
(.branch 752 10287
.empty
.empty)))))
(.branch 771 10224
(.branch 762 10332
(.branch 758 10223
(.branch 756 10351
(.branch 755 10271
(.branch 754 10159
.empty
.empty)
.empty)
(.branch 757 10335
.empty
.empty))
(.branch 760 10204
(.branch 759 10207
.empty
.empty)
(.branch 761 10220
.empty
.empty)))
(.branch 767 10284
(.branch 765 10156
(.branch 764 10268
(.branch 763 10348
.empty
.empty)
.empty)
(.branch 766 10396
.empty
.empty))
(.branch 769 10352
(.branch 768 10336
.empty
.empty)
(.branch 770 10208
.empty
.empty))))
(.branch 780 34547
(.branch 776 34611
(.branch 774 10272
(.branch 773 10288
(.branch 772 10400
.empty
.empty)
.empty)
(.branch 775 10160
.empty
.empty))
(.branch 778 34739
(.branch 777 34595
.empty
.empty)
(.branch 779 34723
.empty
.empty)))
(.branch 785 34719
(.branch 783 34787
(.branch 782 34675
(.branch 781 34659
.empty
.empty)
.empty)
(.branch 784 34735
.empty
.empty))
(.branch 787 34591
(.branch 786 34607
.empty
.empty)
(.branch 788 34671
.empty
.empty))))))
(.branch 825 10313
(.branch 807 34608
(.branch 798 34716
(.branch 794 34780
(.branch 792 34652
(.branch 791 34655
(.branch 790 34543
.empty
.empty)
.empty)
(.branch 793 34540
.empty
.empty))
(.branch 796 34588
(.branch 795 34668
.empty
.empty)
(.branch 797 34604
.empty
.empty)))
(.branch 803 34544
(.branch 801 34672
(.branch 800 34784
(.branch 799 34732
.empty
.empty)
.empty)
(.branch 802 34656
.empty
.empty))
(.branch 805 34736
(.branch 804 34720
.empty
.empty)
(.branch 806 34592
.empty
.empty))))
(.branch 816 34565
(.branch 812 10246
(.branch 810 34570
(.branch 809 10245
(.branch 808 34681
.empty
.empty)
.empty)
(.branch 811 10390
.empty
.empty))
(.branch 814 10389
(.branch 813 34682
.empty
.empty)
(.branch 815 34569
.empty
.empty)))
(.branch 821 34566
(.branch 819 10250
(.branch 818 34710
(.branch 817 10361
.empty
.empty)
.empty)
(.branch 820 10362
.empty
.empty))
(.branch 823 34709
(.branch 822 10249
.empty
.empty)
(.branch 824 34645
.empty
.empty)))))
(.branch 843 10378
(.branch 834 34618
(.branch 830 10169
(.branch 828 10314
(.branch 827 10170
(.branch 826 34758
.empty
.empty)
.empty)
(.branch 829 34646
.empty
.empty))
(.branch 832 34761
(.branch 831 34757
.empty
.empty)
(.branch 833 10197
.empty
.empty)))
(.branch 839 34617
(.branch 837 34762
(.branch 836 10198
(.branch 835 10310
.empty
.empty)
.empty)
(.branch 838 10309
.empty
.empty))
(.branch 841 10233
(.branch 840 34693
.empty
.empty)
(.branch 842 34582
.empty
.empty))))
(.branch 852 10374
(.branch 848 34553
(.branch 846 10377
(.branch 845 34694
(.branch 844 10234
.empty
.empty)
.empty)
(.branch 847 34581
.empty
.empty))
(.branch 850 34698
(.branch 849 10373
.empty
.empty)
(.branch 851 10262
.empty
.empty)))
(.branch 856 34633
(.branch 854 10261
(.branch 853 34554
.empty
.empty)
(.branch 855 34697
.empty
.empty))
(.branch 858 34746
(.branch 857 10325
.empty
.empty)
(.branch 859 10182
.empty
.empty))))))))
(.branch 1003 16493
(.branch 932 13423
(.branch 896 37619
(.branch 878 13404
(.branch 869 34774
(.branch 865 10185
(.branch 863 34745
(.branch 862 10181
(.branch 861 34634
.empty
.empty)
.empty)
(.branch 864 34773
.empty
.empty))
(.branch 867 10298
(.branch 866 34630
.empty
.empty)
(.branch 868 10186
.empty
.empty)))
(.branch 874 37852
(.branch 872 37724
(.branch 871 34629
(.branch 870 10297
.empty
.empty)
.empty)
(.branch 873 37612
.empty
.empty))
(.branch 876 13276
(.branch 875 37740
.empty
.empty)
(.branch 877 13292
.empty
.empty))))
(.branch 887 13475
(.branch 883 37795
(.branch 881 37667
(.branch 880 37683
(.branch 879 13420
.empty
.empty)
.empty)
(.branch 882 37811
.empty
.empty))
(.branch 885 13347
(.branch 884 13235
.empty
.empty)
(.branch 886 13363
.empty
.empty)))
(.branch 892 13340
(.branch 890 37788
(.branch 889 37676
(.branch 888 37660
.empty
.empty)
.empty)
(.branch 891 37804
.empty
.empty))
(.branch 894 13468
(.branch 893 13228
.empty
.empty)
(.branch 895 13356
.empty
.empty)))))
(.branch 914 37679
(.branch 905 37744
(.branch 901 13283
(.branch 899 37859
(.branch 898 37747
(.branch 897 37731
.empty
.empty)
.empty)
(.branch 900 13299
.empty
.empty))
(.branch 903 13411
(.branch 902 13427
.empty
.empty)
(.branch 904 37856
.empty
.empty)))
(.branch 910 13280
(.branch 908 13408
(.branch 907 37616
(.branch 906 37728
.empty
.empty)
.empty)
(.branch 909 13424
.empty
.empty))
(.branch 912 37807
(.branch 911 13296
.empty
.empty)
(.branch 913 37791
.empty
.empty))))
(.branch 923 37680
(.branch 919 13343
(.branch 917 13471
(.branch 916 13359
(.branch 915 37663
.empty
.empty)
.empty)
(.branch 918 13231
.empty
.empty))
(.branch 921 37808
(.branch 920 37792
.empty
.empty)
(.branch 922 37664
.empty
.empty)))
(.branch 928 37743
(.branch 926 13344
(.branch 925 13360
(.branch 924 13472
.empty
.empty)
.empty)
(.branch 927 13232
.empty
.empty))
(.branch 930 37615
(.branch 929 37855
.empty
.empty)
(.branch 931 37727
.empty
.empty))))))
(.branch 968 37637
(.branch 950 13369
(.branch 941 37834
(.branch 937 37638
(.branch 935 13279
(.branch 934 13295
(.branch 933 13407
.empty
.empty)
.empty)
(.branch 936 13434
.empty
.empty))
(.branch 939 37781
(.branch 938 13321
.empty
.empty)
(.branch 940 13270
.empty
.empty)))
(.branch 946 13333
(.branch 944 13446
(.branch 943 37689
(.branch 942 13381
.empty
.empty)
.empty)
(.branch 945 37626
.empty
.empty))
(.branch 948 13258
(.branch 947 37769
.empty
.empty)
(.branch 949 37846
.empty
.empty))))
(.branch 959 37829
(.branch 955 37641
(.branch 953 37754
(.branch 952 13318
(.branch 951 37701
.empty
.empty)
.empty)
(.branch 954 13461
.empty
.empty))
(.branch 957 37718
(.branch 956 13386
.empty
.empty)
(.branch 958 13241
.empty
.empty)))
(.branch 964 13398
(.branch 962 13449
(.branch 961 37766
(.branch 960 13306
.empty
.empty)
.empty)
(.branch 963 37653
.empty
.empty))
(.branch 966 13253
(.branch 965 37706
.empty
.empty)
(.branch 967 37817
.empty
.empty)))))
(.branch 986 37642
(.branch 977 13445
(.branch 973 13269
(.branch 971 13322
(.branch 970 37782
(.branch 969 13433
.empty
.empty)
.empty)
(.branch 972 37833
.empty
.empty))
(.branch 975 13382
(.branch 974 37690
.empty
.empty)
(.branch 976 37625
.empty
.empty)))
(.branch 982 37702
(.branch 980 37845
(.branch 979 13334
(.branch 978 37770
.empty
.empty)
.empty)
(.branch 981 13257
.empty
.empty))
(.branch 984 37753
(.branch 983 13370
.empty
.empty)
(.branch 985 13317
.empty
.empty))))
(.branch 995 13450
(.branch 991 13242
(.branch 989 13385
(.branch 988 37717
(.branch 987 13462
.empty
.empty)
.empty)
(.branch 990 37830
.empty
.empty))
(.branch 993 13305
(.branch 992 37765
.empty
.empty)
(.branch 994 37654
.empty
.empty)))
(.branch 999 13254
(.branch 997 13397
(.branch 996 37705
.empty
.empty)
(.branch 998 37818
.empty
.empty))
(.branch 1001 16482
(.branch 1000 16434
.empty
.empty)
(.branch 1002 16541
.empty
.empty)))))))
(.branch 1075 16391
(.branch 1039 40689
(.branch 1021 16481
(.branch 1012 40754
(.branch 1008 16370
(.branch 1006 40925
(.branch 1005 40866
(.branch 1004 40818
.empty
.empty)
.empty)
(.branch 1007 40877
.empty
.empty))
(.branch 1010 16349
(.branch 1009 16418
.empty
.empty)
(.branch 1011 16301
.empty
.empty)))
(.branch 1017 40865
(.branch 1015 40685
(.branch 1014 40733
(.branch 1013 40802
.empty
.empty)
.empty)
(.branch 1016 40817
.empty
.empty))
(.branch 1019 40878
(.branch 1018 40926
.empty
.empty)
(.branch 1020 16433
.empty
.empty))))
(.branch 1030 16350
(.branch 1026 40734
(.branch 1024 40753
(.branch 1023 16494
(.branch 1022 16542
.empty
.empty)
.empty)
(.branch 1025 40801
.empty
.empty))
(.branch 1028 16369
(.branch 1027 40686
.empty
.empty)
(.branch 1029 16417
.empty
.empty)))
(.branch 1035 16305
(.branch 1033 16414
(.branch 1032 16366
(.branch 1031 16302
.empty
.empty)
.empty)
(.branch 1034 16353
.empty
.empty))
(.branch 1037 40798
(.branch 1036 40750
.empty
.empty)
(.branch 1038 40737
.empty
.empty)))))
(.branch 1057 40861
(.branch 1048 40749
(.branch 1044 40814
(.branch 1042 16545
(.branch 1041 16478
(.branch 1040 16430
.empty
.empty)
.empty)
(.branch 1043 16497
.empty
.empty))
(.branch 1046 40929
(.branch 1045 40862
.empty
.empty)
(.branch 1047 40881
.empty
.empty)))
(.branch 1053 16413
(.branch 1051 40690
(.branch 1050 40738
(.branch 1049 40797
.empty
.empty)
.empty)
(.branch 1052 16365
.empty
.empty))
(.branch 1055 16306
(.branch 1054 16354
.empty
.empty)
(.branch 1056 40813
.empty
.empty))))
(.branch 1066 40712
(.branch 1062 16546
(.branch 1060 16429
(.branch 1059 40882
(.branch 1058 40930
.empty
.empty)
.empty)
(.branch 1061 16477
.empty
.empty))
(.branch 1064 40724
(.branch 1063 16498
.empty
.empty)
(.branch 1065 16520
.empty
.empty)))
(.branch 1071 16312
(.branch 1069 16324
(.branch 1068 40888
(.branch 1067 16532
.empty
.empty)
.empty)
(.branch 1070 40900
.empty
.empty))
(.branch 1073 16379
(.branch 1072 40839
.empty
.empty)
(.branch 1074 40827
.empty
.empty))))))
(.branch 1111 16407
(.branch 1093 16331
(.branch 1084 40772
(.branch 1080 40840
(.branch 1078 40791
(.branch 1077 16471
(.branch 1076 40779
.empty
.empty)
.empty)
(.branch 1079 16459
.empty
.empty))
(.branch 1082 40852
(.branch 1081 16404
.empty
.empty)
(.branch 1083 16392
.empty
.empty)))
(.branch 1089 16519
(.branch 1087 16452
(.branch 1086 40760
(.branch 1085 16440
.empty
.empty)
.empty)
(.branch 1088 40699
.empty
.empty))
(.branch 1091 16507
(.branch 1090 40711
.empty
.empty)
(.branch 1092 40919
.empty
.empty))))
(.branch 1102 40696
(.branch 1098 40916
(.branch 1096 40904
(.branch 1095 16343
(.branch 1094 40907
.empty
.empty)
.empty)
(.branch 1097 16340
.empty
.empty))
(.branch 1100 40708
(.branch 1099 16328
.empty
.empty)
(.branch 1101 16504
.empty
.empty)))
(.branch 1107 16443
(.branch 1105 16455
(.branch 1104 40763
(.branch 1103 16516
.empty
.empty)
.empty)
(.branch 1106 40775
.empty
.empty))
(.branch 1109 16395
(.branch 1108 40855
.empty
.empty)
(.branch 1110 40843
.empty
.empty)))))
(.branch 1129 37671
(.branch 1120 40903
(.branch 1116 40824
(.branch 1114 40776
(.branch 1113 16456
(.branch 1112 40788
.empty
.empty)
.empty)
(.branch 1115 16468
.empty
.empty))
(.branch 1118 40836
(.branch 1117 16388
.empty
.empty)
(.branch 1119 16376
.empty
.empty)))
(.branch 1125 16535
(.branch 1123 16327
(.branch 1122 40891
(.branch 1121 16315
.empty
.empty)
.empty)
(.branch 1124 40715
.empty
.empty))
(.branch 1127 16523
(.branch 1126 40727
.empty
.empty)
(.branch 1128 37803
.empty
.empty))))
(.branch 1138 37732
(.branch 1134 13412
(.branch 1132 13239
(.branch 1131 37748
(.branch 1130 37720
.empty
.empty)
.empty)
(.branch 1133 13467
.empty
.empty))
(.branch 1136 37815
(.branch 1135 13288
.empty
.empty)
(.branch 1137 37659
.empty
.empty)))
(.branch 1142 13400
(.branch 1140 13227
(.branch 1139 37736
.empty
.empty)
(.branch 1141 13479
.empty
.empty))
(.branch 1144 37687
(.branch 1143 13300
.empty
.empty)
(.branch 1145 37787
.empty
.empty))))))))))
(.branch 1719 613
(.branch 1433 33056
(.branch 1290 40720
(.branch 1218 37825
(.branch 1182 13476
(.branch 1164 13419
(.branch 1155 37620
(.branch 1151 13428
(.branch 1149 13351
(.branch 1148 13355
(.branch 1147 37608
.empty
.empty)
.empty)
(.branch 1150 13272
.empty
.empty))
(.branch 1153 37799
(.branch 1152 37675
.empty
.empty)
(.branch 1154 37848
.empty
.empty)))
(.branch 1160 37623
(.branch 1158 13284
(.branch 1157 13339
(.branch 1156 13367
.empty
.empty)
.empty)
(.branch 1159 13416
.empty
.empty))
(.branch 1162 37796
(.branch 1161 37851
.empty
.empty)
(.branch 1163 37672
.empty
.empty))))
(.branch 1173 13275
(.branch 1169 37863
(.branch 1167 13364
(.branch 1166 13336
(.branch 1165 13287
.empty
.empty)
.empty)
(.branch 1168 37611
.empty
.empty))
(.branch 1171 37684
(.branch 1170 37784
.empty
.empty)
(.branch 1172 13431
.empty
.empty)))
(.branch 1178 37656
(.branch 1176 37739
(.branch 1175 13352
(.branch 1174 13348
.empty
.empty)
.empty)
(.branch 1177 37735
.empty
.empty))
(.branch 1180 13303
(.branch 1179 37812
.empty
.empty)
(.branch 1181 13403
.empty
.empty)))))
(.branch 1200 13250
(.branch 1191 13236
(.branch 1187 37800
(.branch 1185 37723
(.branch 1184 37751
(.branch 1183 13224
.empty
.empty)
.empty)
(.branch 1186 37668
.empty
.empty))
(.branch 1189 13415
(.branch 1188 13291
.empty
.empty)
(.branch 1190 13464
.empty
.empty)))
(.branch 1196 13309
(.branch 1194 13389
(.branch 1193 37709
(.branch 1192 13325
.empty
.empty)
.empty)
(.branch 1195 37773
.empty
.empty))
(.branch 1198 13373
(.branch 1197 37693
.empty
.empty)
(.branch 1199 37757
.empty
.empty))))
(.branch 1209 13326
(.branch 1205 37650
(.branch 1203 37826
(.branch 1202 13442
(.branch 1201 37634
.empty
.empty)
.empty)
(.branch 1204 13266
.empty
.empty))
(.branch 1207 37842
(.branch 1206 13458
.empty
.empty)
(.branch 1208 37710
.empty
.empty)))
(.branch 1214 37758
(.branch 1212 37694
(.branch 1211 13390
(.branch 1210 37774
.empty
.empty)
.empty)
(.branch 1213 13310
.empty
.empty))
(.branch 1216 37633
(.branch 1215 13374
.empty
.empty)
(.branch 1217 13249
.empty
.empty))))))
(.branch 1254 37645
(.branch 1236 13454
(.branch 1227 37713
(.branch 1223 13457
(.branch 1221 13265
(.branch 1220 37649
(.branch 1219 13441
.empty
.empty)
.empty)
(.branch 1222 37841
.empty
.empty))
(.branch 1225 37777
(.branch 1224 13393
.empty
.empty)
(.branch 1226 13329
.empty
.empty)))
(.branch 1232 13438
(.branch 1230 13313
(.branch 1229 37761
(.branch 1228 13377
.empty
.empty)
.empty)
(.branch 1231 37697
.empty
.empty))
(.branch 1234 13246
(.branch 1233 37822
.empty
.empty)
(.branch 1235 37630
.empty
.empty))))
(.branch 1245 13378
(.branch 1241 13394
(.branch 1239 37646
(.branch 1238 13262
(.branch 1237 37838
.empty
.empty)
.empty)
(.branch 1240 37778
.empty
.empty))
(.branch 1243 13330
(.branch 1242 37714
.empty
.empty)
(.branch 1244 37762
.empty
.empty)))
(.branch 1250 37629
(.branch 1248 37821
(.branch 1247 13314
(.branch 1246 37698
.empty
.empty)
.empty)
(.branch 1249 13437
.empty
.empty))
(.branch 1252 37837
(.branch 1251 13245
.empty
.empty)
(.branch 1253 13453
.empty
.empty)))))
(.branch 1272 40899
(.branch 1263 16444
(.branch 1259 16524
(.branch 1257 16515
(.branch 1256 40835
(.branch 1255 13261
.empty
.empty)
.empty)
(.branch 1258 40844
.empty
.empty))
(.branch 1261 16467
(.branch 1260 40915
.empty
.empty)
(.branch 1262 40892
.empty
.empty)))
(.branch 1268 40787
(.branch 1266 40716
(.branch 1265 16387
(.branch 1264 40707
.empty
.empty)
.empty)
(.branch 1267 16396
.empty
.empty))
(.branch 1270 40764
(.branch 1269 16339
.empty
.empty)
(.branch 1271 16316
.empty
.empty))))
(.branch 1281 16323
(.branch 1277 16531
(.branch 1275 16460
(.branch 1274 40908
(.branch 1273 16451
.empty
.empty)
.empty)
(.branch 1276 40851
.empty
.empty))
(.branch 1279 16508
(.branch 1278 40828
.empty
.empty)
(.branch 1280 40771
.empty
.empty)))
(.branch 1286 40700
(.branch 1284 40723
(.branch 1283 16332
(.branch 1282 40780
.empty
.empty)
.empty)
(.branch 1285 16403
.empty
.empty))
(.branch 1288 40703
(.branch 1287 16380
.empty
.empty)
(.branch 1289 16383
.empty
.empty)))))))
(.branch 1362 40757
(.branch 1326 40933
(.branch 1308 40719
(.branch 1299 16528
(.branch 1295 16320
(.branch 1293 16335
(.branch 1292 40783
(.branch 1291 16400
.empty
.empty)
.empty)
(.branch 1294 40768
.empty
.empty))
(.branch 1297 16511
(.branch 1296 40831
.empty
.empty)
(.branch 1298 40848
.empty
.empty)))
(.branch 1304 40767
(.branch 1302 40896
(.branch 1301 16463
(.branch 1300 40911
.empty
.empty)
.empty)
(.branch 1303 16448
.empty
.empty))
(.branch 1306 40784
(.branch 1305 16319
.empty
.empty)
(.branch 1307 16336
.empty
.empty))))
(.branch 1317 16527
(.branch 1313 16447
(.branch 1311 16384
(.branch 1310 40704
(.branch 1309 16399
.empty
.empty)
.empty)
(.branch 1312 40895
.empty
.empty))
(.branch 1315 16464
(.branch 1314 40912
.empty
.empty)
(.branch 1316 40847
.empty
.empty)))
(.branch 1322 16345
(.branch 1320 16357
(.branch 1319 16512
(.branch 1318 40832
.empty
.empty)
.empty)
(.branch 1321 16489
.empty
.empty))
(.branch 1324 40921
(.branch 1323 16501
.empty
.empty)
(.branch 1325 40693
.empty
.empty)))))
(.branch 1344 16298
(.branch 1335 40858
(.branch 1331 16422
(.branch 1329 16410
(.branch 1328 16438
(.branch 1327 40681
.empty
.empty)
.empty)
(.branch 1330 16426
.empty
.empty))
(.branch 1333 40870
(.branch 1332 40746
.empty
.empty)
(.branch 1334 40758
.empty
.empty)))
(.branch 1340 40805
(.branch 1338 16485
(.branch 1337 16373
(.branch 1336 16473
.empty
.empty)
.empty)
(.branch 1339 16361
.empty
.empty))
(.branch 1342 40793
(.branch 1341 40809
.empty
.empty)
(.branch 1343 40821
.empty
.empty))))
(.branch 1353 40694
(.branch 1349 40730
(.branch 1347 16538
(.branch 1346 16310
(.branch 1345 16550
.empty
.empty)
.empty)
(.branch 1348 40886
.empty
.empty))
(.branch 1351 40742
(.branch 1350 40874
.empty
.empty)
(.branch 1352 40922
.empty
.empty)))
(.branch 1358 16346
(.branch 1356 16358
(.branch 1355 40682
(.branch 1354 40934
.empty
.empty)
.empty)
(.branch 1357 16490
.empty
.empty))
(.branch 1360 40745
(.branch 1359 16502
.empty
.empty)
(.branch 1361 40869
.empty
.empty))))))
(.branch 1398 350
(.branch 1380 16297
(.branch 1371 40822
(.branch 1367 16421
(.branch 1365 16409
(.branch 1364 16437
(.branch 1363 40857
.empty
.empty)
.empty)
(.branch 1366 16425
.empty
.empty))
(.branch 1369 40810
(.branch 1368 40806
.empty
.empty)
(.branch 1370 40794
.empty
.empty)))
(.branch 1376 40885
(.branch 1374 16486
(.branch 1373 16374
(.branch 1372 16474
.empty
.empty)
.empty)
(.branch 1375 16362
.empty
.empty))
(.branch 1378 40873
(.branch 1377 40729
.empty
.empty)
(.branch 1379 40741
.empty
.empty))))
(.branch 1389 33014
(.branch 1385 55
(.branch 1383 16537
(.branch 1382 16309
(.branch 1381 16549
.empty
.empty)
.empty)
(.branch 1384 33013
.empty
.empty))
(.branch 1387 332
(.branch 1386 33034
.empty
.empty)
(.branch 1388 75
.empty
.empty)))
(.branch 1394 33061
(.branch 1392 33029
(.branch 1391 33033
(.branch 1390 352
.empty
.empty)
.empty)
(.branch 1393 57
.empty
.empty))
(.branch 1396 77
(.branch 1395 330
.empty
.empty)
(.branch 1397 33030
.empty
.empty)))))
(.branch 1416 12
(.branch 1407 33017
(.branch 1403 333
(.branch 1401 54
(.branch 1400 33050
(.branch 1399 33062
.empty
.empty)
.empty)
(.branch 1402 33018
.empty
.empty))
(.branch 1405 33049
(.branch 1404 74
.empty
.empty)
(.branch 1406 353
.empty
.empty)))
(.branch 1412 76
(.branch 1410 33002
(.branch 1409 56
(.branch 1408 33045
.empty
.empty)
.empty)
(.branch 1411 331
.empty
.empty))
(.branch 1414 351
(.branch 1413 33046
.empty
.empty)
(.branch 1415 33001
.empty
.empty))))
(.branch 1425 33023
(.branch 1421 34
(.branch 1419 33040
(.branch 1418 289
(.branch 1417 33007
.empty
.empty)
.empty)
(.branch 1420 33011
.empty
.empty))
(.branch 1423 311
(.branch 1422 33036
.empty
.empty)
(.branch 1424 14
.empty
.empty)))
(.branch 1429 36
(.branch 1427 33055
(.branch 1426 287
.empty
.empty)
(.branch 1428 33027
.empty
.empty))
(.branch 1431 309
(.branch 1430 33059
.empty
.empty)
(.branch 1432 11
.empty
.empty))))))))
(.branch 1576 10283
(.branch 1505 1142
(.branch 1469 419
(.branch 1451 89
(.branch 1442 288
(.branch 1438 33020
(.branch 1436 33052
(.branch 1435 33024
(.branch 1434 290
.empty
.empty)
.empty)
(.branch 1437 33
.empty
.empty))
(.branch 1440 13
(.branch 1439 312
.empty
.empty)
(.branch 1441 33039
.empty
.empty)))
(.branch 1447 310
(.branch 1445 35
(.branch 1444 33043
(.branch 1443 33008
.empty
.empty)
.empty)
(.branch 1446 33004
.empty
.empty))
(.branch 1449 416
(.branch 1448 1152
.empty
.empty)
(.branch 1450 1158
.empty
.empty))))
(.branch 1460 384
(.branch 1456 1157
(.branch 1454 366
(.branch 1453 1167
(.branch 1452 141
.empty
.empty)
.empty)
(.branch 1455 1161
.empty
.empty))
(.branch 1458 1148
(.branch 1457 107
.empty
.empty)
(.branch 1459 400
.empty
.empty)))
(.branch 1465 1135
(.branch 1463 1171
(.branch 1462 125
(.branch 1461 1162
.empty
.empty)
.empty)
(.branch 1464 142
.empty
.empty))
(.branch 1467 1129
(.branch 1466 367
.empty
.empty)
(.branch 1468 1183
.empty
.empty)))))
(.branch 1487 1173
(.branch 1478 1187
(.branch 1474 126
(.branch 1472 385
(.branch 1471 92
(.branch 1470 1177
.empty
.empty)
.empty)
(.branch 1473 1130
.empty
.empty))
(.branch 1476 1178
(.branch 1475 1139
.empty
.empty)
(.branch 1477 110
.empty
.empty)))
(.branch 1483 383
(.branch 1481 124
(.branch 1480 1155
(.branch 1479 403
.empty
.empty)
.empty)
(.branch 1482 1146
.empty
.empty))
(.branch 1485 1164
(.branch 1484 401
.empty
.empty)
(.branch 1486 108
.empty
.empty))))
(.branch 1496 402
(.branch 1492 90
(.branch 1490 1151
(.branch 1489 365
(.branch 1488 1145
.empty
.empty)
.empty)
(.branch 1491 140
.empty
.empty))
(.branch 1494 417
(.branch 1493 1174
.empty
.empty)
(.branch 1495 1168
.empty
.empty)))
(.branch 1501 127
(.branch 1499 1141
(.branch 1498 109
(.branch 1497 1132
.empty
.empty)
.empty)
(.branch 1500 1180
.empty
.empty))
(.branch 1503 386
(.branch 1502 1189
.empty
.empty)
(.branch 1504 91
.empty
.empty))))))
(.branch 1541 34705
(.branch 1523 10173
(.branch 1514 34753
(.branch 1510 1184
(.branch 1508 1190
(.branch 1507 1136
(.branch 1506 418
.empty
.empty)
.empty)
(.branch 1509 368
.empty
.empty))
(.branch 1512 34561
(.branch 1511 143
.empty
.empty)
(.branch 1513 10177
.empty
.empty)))
(.branch 1519 34754
(.branch 1517 34562
(.branch 1516 10178
(.branch 1515 10369
.empty
.empty)
.empty)
(.branch 1518 10370
.empty
.empty))
(.branch 1521 10365
(.branch 1520 34749
.empty
.empty)
(.branch 1522 34557
.empty
.empty))))
(.branch 1532 10253
(.branch 1528 34638
(.branch 1526 10174
(.branch 1525 34750
(.branch 1524 10366
.empty
.empty)
.empty)
(.branch 1527 34558
.empty
.empty))
(.branch 1530 34702
(.branch 1529 10254
.empty
.empty)
(.branch 1531 10318
.empty
.empty)))
(.branch 1537 10322
(.branch 1535 34701
(.branch 1534 10317
(.branch 1533 34637
.empty
.empty)
.empty)
(.branch 1536 34706
.empty
.empty))
(.branch 1539 10258
(.branch 1538 34642
.empty
.empty)
(.branch 1540 10321
.empty
.empty)))))
(.branch 1559 34574
(.branch 1550 10386
(.branch 1546 34769
(.branch 1544 34577
(.branch 1543 34641
(.branch 1542 10257
.empty
.empty)
.empty)
(.branch 1545 10193
.empty
.empty))
(.branch 1548 10194
(.branch 1547 10385
.empty
.empty)
(.branch 1549 34578
.empty
.empty)))
(.branch 1555 10189
(.branch 1553 10381
(.branch 1552 34765
(.branch 1551 34770
.empty
.empty)
.empty)
(.branch 1554 34573
.empty
.empty))
(.branch 1557 34766
(.branch 1556 10382
.empty
.empty)
(.branch 1558 10190
.empty
.empty))))
(.branch 1568 34690
(.branch 1564 10237
(.branch 1562 34686
(.branch 1561 10238
(.branch 1560 34622
.empty
.empty)
.empty)
(.branch 1563 10302
.empty
.empty))
(.branch 1566 10301
(.branch 1565 34621
.empty
.empty)
(.branch 1567 34685
.empty
.empty)))
(.branch 1572 10305
(.branch 1570 34626
(.branch 1569 10306
.empty
.empty)
(.branch 1571 10242
.empty
.empty))
(.branch 1574 10241
(.branch 1573 34689
.empty
.empty)
(.branch 1575 34625
.empty
.empty)))))))
(.branch 1648 33226
(.branch 1612 10219
(.branch 1594 34788
(.branch 1585 10395
(.branch 1581 10331
(.branch 1579 10356
(.branch 1578 10200
(.branch 1577 10279
.empty
.empty)
.empty)
(.branch 1580 10231
.empty
.empty))
(.branch 1583 10152
(.branch 1582 10404
.empty
.empty)
(.branch 1584 10167
.empty
.empty)))
(.branch 1590 10264
(.branch 1588 10347
(.branch 1587 10216
(.branch 1586 10340
.empty
.empty)
.empty)
(.branch 1589 10215
.empty
.empty))
(.branch 1592 34615
(.branch 1591 10292
.empty
.empty)
(.branch 1593 34715
.empty
.empty))))
(.branch 1603 34676
(.branch 1599 34740
(.branch 1597 34663
(.branch 1596 34667
(.branch 1595 34536
.empty
.empty)
.empty)
(.branch 1598 34584
.empty
.empty))
(.branch 1601 34599
(.branch 1600 34731
.empty
.empty)
(.branch 1602 34648
.empty
.empty)))
(.branch 1608 10295
(.branch 1606 34724
(.branch 1605 34779
(.branch 1604 34551
.empty
.empty)
.empty)
(.branch 1607 34600
.empty
.empty))
(.branch 1610 10212
(.branch 1609 10267
.empty
.empty)
(.branch 1611 10344
.empty
.empty)))))
(.branch 1630 34596
(.branch 1621 10203
(.branch 1617 10407
(.branch 1615 10164
(.branch 1614 10392
(.branch 1613 10343
.empty
.empty)
.empty)
(.branch 1616 10155
.empty
.empty))
(.branch 1619 10228
(.branch 1618 10328
.empty
.empty)
(.branch 1620 10359
.empty
.empty)))
(.branch 1626 34776
(.branch 1624 34603
(.branch 1623 10280
(.branch 1622 10276
.empty
.empty)
.empty)
(.branch 1625 34727
.empty
.empty))
(.branch 1628 34679
(.branch 1627 34548
.empty
.empty)
(.branch 1629 34651
.empty
.empty))))
(.branch 1639 34612
(.branch 1635 34664
(.branch 1633 34587
(.branch 1632 34743
(.branch 1631 34728
.empty
.empty)
.empty)
(.branch 1634 34660
.empty
.empty))
(.branch 1637 34791
(.branch 1636 34539
.empty
.empty)
(.branch 1638 34712
.empty
.empty)))
(.branch 1644 345
(.branch 1642 33210
(.branch 1641 325
(.branch 1640 33242
.empty
.empty)
.empty)
(.branch 1643 46
.empty
.empty))
(.branch 1646 66
(.branch 1645 33241
.empty
.empty)
(.branch 1647 33209
.empty
.empty))))))
(.branch 1684 342
(.branch 1666 281
(.branch 1657 33248
(.branch 1653 33225
(.branch 1651 324
(.branch 1650 33205
(.branch 1649 47
.empty
.empty)
.empty)
(.branch 1652 67
.empty
.empty))
(.branch 1655 33206
(.branch 1654 344
.empty
.empty)
(.branch 1656 282
.empty
.empty)))
(.branch 1662 33212
(.branch 1660 33244
(.branch 1659 33216
(.branch 1658 3
.empty
.empty)
.empty)
(.branch 1661 304
.empty
.empty))
(.branch 1664 4
(.branch 1663 25
.empty
.empty)
(.branch 1665 33232
.empty
.empty))))
(.branch 1675 323
(.branch 1671 303
(.branch 1669 26
(.branch 1668 33228
(.branch 1667 33199
.empty
.empty)
.empty)
(.branch 1670 33203
.empty
.empty))
(.branch 1673 48
(.branch 1672 33194
.empty
.empty)
(.branch 1674 33237
.empty
.empty)))
(.branch 1680 33221
(.branch 1678 343
(.branch 1677 33193
(.branch 1676 68
.empty
.empty)
.empty)
(.branch 1679 33238
.empty
.empty))
(.branch 1682 33253
(.branch 1681 322
.empty
.empty)
(.branch 1683 49
.empty
.empty)))))
(.branch 1702 33251
(.branch 1693 27
(.branch 1689 33200
(.branch 1687 33254
(.branch 1686 69
(.branch 1685 33222
.empty
.empty)
.empty)
(.branch 1688 5
.empty
.empty))
(.branch 1691 33231
(.branch 1690 280
.empty
.empty)
(.branch 1692 33196
.empty
.empty)))
(.branch 1698 6
(.branch 1696 279
(.branch 1695 302
(.branch 1694 33235
.empty
.empty)
.empty)
(.branch 1697 33215
.empty
.empty))
(.branch 1700 33219
(.branch 1699 33247
.empty
.empty)
(.branch 1701 301
.empty
.empty))))
(.branch 1711 464
(.branch 1707 437
(.branch 1705 559
(.branch 1704 553
(.branch 1703 28
.empty
.empty)
.empty)
(.branch 1706 200
.empty
.empty))
(.branch 1709 565
(.branch 1708 556
.empty
.empty)
(.branch 1710 175
.empty
.empty)))
(.branch 1715 607
(.branch 1713 162
(.branch 1712 477
.empty
.empty)
(.branch 1714 601
.empty
.empty))
(.branch 1717 189
(.branch 1716 452
.empty
.empty)
(.branch 1718 604
.empty
.empty)))))))))
(.branch 2006 37657
(.branch 1863 16360
(.branch 1791 40914
(.branch 1755 572
(.branch 1737 563
(.branch 1728 585
(.branch 1724 449
(.branch 1722 582
(.branch 1721 159
(.branch 1720 474
.empty
.empty)
.empty)
(.branch 1723 576
.empty
.empty))
(.branch 1726 579
(.branch 1725 186
.empty
.empty)
(.branch 1727 570
.empty
.empty)))
(.branch 1733 597
(.branch 1731 436
(.branch 1730 199
(.branch 1729 591
.empty
.empty)
.empty)
(.branch 1732 588
.empty
.empty))
(.branch 1735 463
(.branch 1734 174
.empty
.empty)
(.branch 1736 554
.empty
.empty))))
(.branch 1746 602
(.branch 1742 161
(.branch 1740 560
(.branch 1739 451
(.branch 1738 188
.empty
.empty)
.empty)
(.branch 1741 566
.empty
.empty))
(.branch 1744 465
(.branch 1743 476
.empty
.empty)
(.branch 1745 176
.empty
.empty)))
(.branch 1751 614
(.branch 1749 201
(.branch 1748 438
(.branch 1747 611
.empty
.empty)
.empty)
(.branch 1750 608
.empty
.empty))
(.branch 1753 173
(.branch 1752 462
.empty
.empty)
(.branch 1754 581
.empty
.empty)))))
(.branch 1773 16466
(.branch 1764 592
(.branch 1760 586
(.branch 1758 575
(.branch 1757 198
(.branch 1756 435
.empty
.empty)
.empty)
(.branch 1759 569
.empty
.empty))
(.branch 1762 187
(.branch 1761 595
.empty
.empty)
(.branch 1763 450
.empty
.empty)))
(.branch 1769 40894
(.branch 1767 475
(.branch 1766 160
(.branch 1765 598
.empty
.empty)
.empty)
(.branch 1768 16525
.empty
.empty))
(.branch 1771 40893
(.branch 1770 16526
.empty
.empty)
(.branch 1772 40833
.empty
.empty))))
(.branch 1782 16385
(.branch 1778 40717
(.branch 1776 40718
(.branch 1775 16465
(.branch 1774 40834
.empty
.empty)
.empty)
(.branch 1777 16317
.empty
.empty))
(.branch 1780 16386
(.branch 1779 16318
.empty
.empty)
(.branch 1781 40785
.empty
.empty)))
(.branch 1787 16446
(.branch 1785 16445
(.branch 1784 40846
(.branch 1783 40786
.empty
.empty)
.empty)
(.branch 1786 40845
.empty
.empty))
(.branch 1789 40913
(.branch 1788 16514
.empty
.empty)
(.branch 1790 16513
.empty
.empty))))))
(.branch 1827 16382
(.branch 1809 40702
(.branch 1800 40910
(.branch 1796 40705
(.branch 1794 16398
(.branch 1793 40766
(.branch 1792 16397
.empty
.empty)
.empty)
(.branch 1795 40765
.empty
.empty))
(.branch 1798 40706
(.branch 1797 16338
.empty
.empty)
(.branch 1799 16337
.empty
.empty)))
(.branch 1805 40849
(.branch 1803 16510
(.branch 1802 40909
(.branch 1801 16509
.empty
.empty)
.empty)
(.branch 1804 16450
.empty
.empty))
(.branch 1807 40850
(.branch 1806 16449
.empty
.empty)
(.branch 1808 16333
.empty
.empty))))
(.branch 1818 16462
(.branch 1814 40770
(.branch 1812 40769
(.branch 1811 40701
(.branch 1810 16334
.empty
.empty)
.empty)
(.branch 1813 16402
.empty
.empty))
(.branch 1816 16461
(.branch 1815 16401
.empty
.empty)
(.branch 1817 40830
.empty
.empty)))
(.branch 1823 16529
(.branch 1821 16530
(.branch 1820 40897
(.branch 1819 40829
.empty
.empty)
.empty)
(.branch 1822 40898
.empty
.empty))
(.branch 1825 16381
(.branch 1824 40782
.empty
.empty)
(.branch 1826 40781
.empty
.empty)))))
(.branch 1845 16484
(.branch 1836 40875
(.branch 1832 40747
(.branch 1830 16321
(.branch 1829 40721
(.branch 1828 16322
.empty
.empty)
.empty)
(.branch 1831 40722
.empty
.empty))
(.branch 1834 40731
(.branch 1833 16299
.empty
.empty)
(.branch 1835 16411
.empty
.empty)))
(.branch 1841 16356
(.branch 1839 16539
(.branch 1838 40859
(.branch 1837 16427
.empty
.empty)
.empty)
(.branch 1840 40804
.empty
.empty))
(.branch 1843 16372
(.branch 1842 40692
.empty
.empty)
(.branch 1844 40932
.empty
.empty))))
(.branch 1854 40743
(.branch 1850 40871
(.branch 1848 40887
(.branch 1847 16500
(.branch 1846 40820
.empty
.empty)
.empty)
(.branch 1849 16439
.empty
.empty))
(.branch 1852 40759
(.branch 1851 16551
.empty
.empty)
(.branch 1853 16311
.empty
.empty)))
(.branch 1859 16488
(.branch 1857 16472
(.branch 1856 40920
(.branch 1855 16423
.empty
.empty)
.empty)
(.branch 1858 40808
.empty
.empty))
(.branch 1861 16344
(.branch 1860 40792
.empty
.empty)
(.branch 1862 40680
.empty
.empty)))))))
(.branch 1935 37696
(.branch 1899 37772
(.branch 1881 16503
(.branch 1872 40740
(.branch 1868 40811
(.branch 1866 40795
(.branch 1865 16363
(.branch 1864 40683
.empty
.empty)
.empty)
(.branch 1867 16347
.empty
.empty))
(.branch 1870 40923
(.branch 1869 16491
.empty
.empty)
(.branch 1871 16475
.empty
.empty)))
(.branch 1877 16548
(.branch 1875 16308
(.branch 1874 40756
(.branch 1873 16420
.empty
.empty)
.empty)
(.branch 1876 40868
.empty
.empty))
(.branch 1879 16436
(.branch 1878 40884
.empty
.empty)
(.branch 1880 40823
.empty
.empty))))
(.branch 1890 40872
(.branch 1886 40807
(.branch 1884 40695
(.branch 1883 16487
(.branch 1882 40935
.empty
.empty)
.empty)
(.branch 1885 16375
.empty
.empty))
(.branch 1888 40856
(.branch 1887 16359
.empty
.empty)
(.branch 1889 16536
.empty
.empty)))
(.branch 1895 16296
(.branch 1893 16408
(.branch 1892 40728
(.branch 1891 16424
.empty
.empty)
.empty)
(.branch 1894 40744
.empty
.empty))
(.branch 1897 37827
(.branch 1896 37635
.empty
.empty)
(.branch 1898 37708
.empty
.empty)))))
(.branch 1917 37779
(.branch 1908 13267
(.branch 1904 13251
(.branch 1902 37692
(.branch 1901 37843
(.branch 1900 37651
.empty
.empty)
.empty)
(.branch 1903 37756
.empty
.empty))
(.branch 1906 13324
(.branch 1905 13443
.empty
.empty)
(.branch 1907 13388
.empty
.empty)))
(.branch 1913 37763
(.branch 1911 13372
(.branch 1910 13308
(.branch 1909 13459
.empty
.empty)
.empty)
(.branch 1912 37699
.empty
.empty))
(.branch 1915 37836
(.branch 1914 37644
.empty
.empty)
(.branch 1916 37715
.empty
.empty))))
(.branch 1926 13244
(.branch 1922 13260
(.branch 1920 13315
(.branch 1919 37820
(.branch 1918 37628
.empty
.empty)
.empty)
(.branch 1921 13379
.empty
.empty))
(.branch 1924 13331
(.branch 1923 13452
.empty
.empty)
(.branch 1925 13395
.empty
.empty)))
(.branch 1931 37712
(.branch 1929 37631
(.branch 1928 37823
(.branch 1927 13436
.empty
.empty)
.empty)
(.branch 1930 37776
.empty
.empty))
(.branch 1933 37647
(.branch 1932 37839
.empty
.empty)
(.branch 1934 37760
.empty
.empty))))))
(.branch 1971 37737
(.branch 1953 13311
(.branch 1944 37759
(.branch 1940 13455
(.branch 1938 13392
(.branch 1937 13247
(.branch 1936 13439
.empty
.empty)
.empty)
(.branch 1939 13328
.empty
.empty))
(.branch 1942 13376
(.branch 1941 13263
.empty
.empty)
(.branch 1943 13312
.empty
.empty)))
(.branch 1949 37711
(.branch 1947 37648
(.branch 1946 37840
(.branch 1945 37695
.empty
.empty)
.empty)
(.branch 1948 37775
.empty
.empty))
(.branch 1951 37632
(.branch 1950 37824
.empty
.empty)
(.branch 1952 13375
.empty
.empty))))
(.branch 1962 13289
(.branch 1958 13440
(.branch 1956 13391
(.branch 1955 13264
(.branch 1954 13456
.empty
.empty)
.empty)
(.branch 1957 13327
.empty
.empty))
(.branch 1960 13413
(.branch 1959 13248
.empty
.empty)
(.branch 1961 37721
.empty
.empty)))
(.branch 1967 37670
(.branch 1965 37802
(.branch 1964 13238
(.branch 1963 37749
.empty
.empty)
.empty)
(.branch 1966 13466
.empty
.empty))
(.branch 1969 37733
(.branch 1968 13401
.empty
.empty)
(.branch 1970 13301
.empty
.empty)))))
(.branch 1989 37610
(.branch 1980 13418
(.branch 1976 13337
(.branch 1974 13478
(.branch 1973 37814
(.branch 1972 13226
.empty
.empty)
.empty)
(.branch 1975 37658
.empty
.empty))
(.branch 1978 13365
(.branch 1977 37797
.empty
.empty)
(.branch 1979 37673
.empty
.empty)))
(.branch 1985 37785
(.branch 1983 37850
(.branch 1982 13286
(.branch 1981 37622
.empty
.empty)
.empty)
(.branch 1984 13349
.empty
.empty))
(.branch 1987 37685
(.branch 1986 13353
.empty
.empty)
(.branch 1988 13430
.empty
.empty))))
(.branch 1998 37669
(.branch 1994 37750
(.branch 1992 37722
(.branch 1991 37862
(.branch 1990 13274
.empty
.empty)
.empty)
(.branch 1993 13414
.empty
.empty))
(.branch 1996 37801
(.branch 1995 13290
.empty
.empty)
(.branch 1997 13237
.empty
.empty)))
(.branch 2002 37738
(.branch 2000 37734
(.branch 1999 13465
.empty
.empty)
(.branch 2001 13402
.empty
.empty))
(.branch 2004 37813
(.branch 2003 13302
.empty
.empty)
(.branch 2005 13225
.empty
.empty))))))))
(.branch 2149 16495
(.branch 2078 40710
(.branch 2042 16341
(.branch 2024 16378
(.branch 2015 13285
(.branch 2011 13366
(.branch 2009 13338
(.branch 2008 37798
(.branch 2007 13477
.empty
.empty)
.empty)
(.branch 2010 37674
.empty
.empty))
(.branch 2013 13417
(.branch 2012 37621
.empty
.empty)
(.branch 2014 37849
.empty
.empty)))
(.branch 2020 37609
(.branch 2018 37686
(.branch 2017 13350
(.branch 2016 37786
.empty
.empty)
.empty)
(.branch 2019 13354
.empty
.empty))
(.branch 2022 37861
(.branch 2021 13429
.empty
.empty)
(.branch 2023 13273
.empty
.empty))))
(.branch 2033 40826
(.branch 2029 16458
(.branch 2027 16533
(.branch 2026 16521
(.branch 2025 16390
.empty
.empty)
.empty)
(.branch 2028 16470
.empty
.empty))
(.branch 2031 16313
(.branch 2030 16325
.empty
.empty)
(.branch 2032 40838
.empty
.empty)))
(.branch 2038 40889
(.branch 2036 40778
(.branch 2035 40713
(.branch 2034 40725
.empty
.empty)
.empty)
(.branch 2037 40790
.empty
.empty))
(.branch 2040 16454
(.branch 2039 40901
.empty
.empty)
(.branch 2041 16442
.empty
.empty)))))
(.branch 2060 40777
(.branch 2051 40917
(.branch 2047 16517
(.branch 2045 16406
(.branch 2044 16394
(.branch 2043 16329
.empty
.empty)
.empty)
(.branch 2046 16505
.empty
.empty))
(.branch 2049 40774
(.branch 2048 40762
.empty
.empty)
(.branch 2050 40905
.empty
.empty)))
(.branch 2056 40837
(.branch 2054 40709
(.branch 2053 40842
(.branch 2052 40854
.empty
.empty)
.empty)
(.branch 2055 40697
.empty
.empty))
(.branch 2058 40726
(.branch 2057 40825
.empty
.empty)
(.branch 2059 40714
.empty
.empty))))
(.branch 2069 16457
(.branch 2065 16389
(.branch 2063 40902
(.branch 2062 40890
(.branch 2061 40789
.empty
.empty)
.empty)
(.branch 2064 16377
.empty
.empty))
(.branch 2067 16534
(.branch 2066 16522
.empty
.empty)
(.branch 2068 16469
.empty
.empty)))
(.branch 2074 40906
(.branch 2072 40761
(.branch 2071 16314
(.branch 2070 16326
.empty
.empty)
.empty)
(.branch 2073 40773
.empty
.empty))
(.branch 2076 40853
(.branch 2075 40918
.empty
.empty)
(.branch 2077 40841
.empty
.empty))))))
(.branch 2114 40748
(.branch 2096 40732
(.branch 2087 16518
(.branch 2083 16330
(.branch 2081 16441
(.branch 2080 16453
(.branch 2079 40698
.empty
.empty)
.empty)
(.branch 2082 16342
.empty
.empty))
(.branch 2085 16405
(.branch 2084 16393
.empty
.empty)
(.branch 2086 16506
.empty
.empty)))
(.branch 2092 40819
(.branch 2090 40876
(.branch 2089 16540
(.branch 2088 40924
.empty
.empty)
.empty)
(.branch 2091 16492
.empty
.empty))
(.branch 2094 40867
(.branch 2093 16435
.empty
.empty)
(.branch 2095 16483
.empty
.empty))))
(.branch 2105 16476
(.branch 2101 16371
(.branch 2099 16300
(.branch 2098 40684
(.branch 2097 16348
.empty
.empty)
.empty)
(.branch 2100 40755
.empty
.empty))
(.branch 2103 16419
(.branch 2102 40803
.empty
.empty)
(.branch 2104 40860
.empty
.empty)))
(.branch 2110 40931
(.branch 2108 40883
(.branch 2107 16428
(.branch 2106 40812
.empty
.empty)
.empty)
(.branch 2109 16499
.empty
.empty))
(.branch 2112 40796
(.branch 2111 16547
.empty
.empty)
(.branch 2113 16412
.empty
.empty)))))
(.branch 2132 40815
(.branch 2123 16304
(.branch 2119 16355
(.branch 2117 16307
(.branch 2116 40691
(.branch 2115 16364
.empty
.empty)
.empty)
(.branch 2118 40739
.empty
.empty))
(.branch 2121 16352
(.branch 2120 40736
.empty
.empty)
(.branch 2122 40688
.empty
.empty)))
(.branch 2128 40928
(.branch 2126 40799
(.branch 2125 16367
(.branch 2124 40751
.empty
.empty)
.empty)
(.branch 2127 16415
.empty
.empty))
(.branch 2130 40880
(.branch 2129 16544
.empty
.empty)
(.branch 2131 16496
.empty
.empty))))
(.branch 2141 16303
(.branch 2137 16416
(.branch 2135 16479
(.branch 2134 40863
(.branch 2133 16431
.empty
.empty)
.empty)
(.branch 2136 40800
.empty
.empty))
(.branch 2139 16368
(.branch 2138 40752
.empty
.empty)
(.branch 2140 40687
.empty
.empty)))
(.branch 2145 16480
(.branch 2143 16351
(.branch 2142 40735
.empty
.empty)
(.branch 2144 40864
.empty
.empty))
(.branch 2147 16432
(.branch 2146 40816
.empty
.empty)
(.branch 2148 40879
.empty
.empty)))))))
(.branch 2221 10345
(.branch 2185 34691
(.branch 2167 10256
(.branch 2158 10252
(.branch 2154 10188
(.branch 2152 10243
(.branch 2151 16543
(.branch 2150 40927
.empty
.empty)
.empty)
(.branch 2153 10307
.empty
.empty))
(.branch 2156 10179
(.branch 2155 10380
.empty
.empty)
(.branch 2157 10371
.empty
.empty)))
(.branch 2163 10192
(.branch 2161 10239
(.branch 2160 10303
(.branch 2159 10316
.empty
.empty)
.empty)
(.branch 2162 10384
.empty
.empty))
(.branch 2165 10175
(.branch 2164 10367
.empty
.empty)
(.branch 2166 10320
.empty
.empty))))
(.branch 2176 10319
(.branch 2172 10195
(.branch 2170 10172
(.branch 2169 10323
(.branch 2168 10259
.empty
.empty)
.empty)
(.branch 2171 10364
.empty
.empty))
(.branch 2174 10236
(.branch 2173 10387
.empty
.empty)
(.branch 2175 10300
.empty
.empty)))
(.branch 2181 10191
(.branch 2179 10176
(.branch 2178 10368
(.branch 2177 10255
.empty
.empty)
.empty)
(.branch 2180 10383
.empty
.empty))
(.branch 2183 10240
(.branch 2182 10304
.empty
.empty)
(.branch 2184 34627
.empty
.empty)))))
(.branch 2203 34748
(.branch 2194 34768
(.branch 2190 34636
(.branch 2188 34563
(.branch 2187 34764
(.branch 2186 34572
.empty
.empty)
.empty)
(.branch 2189 34755
.empty
.empty))
(.branch 2192 34687
(.branch 2191 34700
.empty
.empty)
(.branch 2193 34623
.empty
.empty)))
(.branch 2199 34640
(.branch 2197 34559
(.branch 2196 34751
(.branch 2195 34576
.empty
.empty)
.empty)
(.branch 2198 34704
.empty
.empty))
(.branch 2201 34707
(.branch 2200 34643
.empty
.empty)
(.branch 2202 34556
.empty
.empty))))
(.branch 2212 34767
(.branch 2208 34703
(.branch 2206 34620
(.branch 2205 34771
(.branch 2204 34579
.empty
.empty)
.empty)
(.branch 2207 34684
.empty
.empty))
(.branch 2210 34752
(.branch 2209 34639
.empty
.empty)
(.branch 2211 34560
.empty
.empty)))
(.branch 2217 10165
(.branch 2215 34624
(.branch 2214 34688
(.branch 2213 34575
.empty
.empty)
.empty)
(.branch 2216 34729
.empty
.empty))
(.branch 2219 10393
(.branch 2218 34597
.empty
.empty)
(.branch 2220 34549
.empty
.empty))))))
(.branch 2257 34742
(.branch 2239 10294
(.branch 2230 10214
(.branch 2226 10394
(.branch 2224 10166
(.branch 2223 10213
(.branch 2222 34777
.empty
.empty)
.empty)
(.branch 2225 34730
.empty
.empty))
(.branch 2228 10346
(.branch 2227 34598
.empty
.empty)
(.branch 2229 34550
.empty
.empty)))
(.branch 2235 10218
(.branch 2233 10342
(.branch 2232 34650
(.branch 2231 34778
.empty
.empty)
.empty)
(.branch 2234 34678
.empty
.empty))
(.branch 2237 10266
(.branch 2236 34726
.empty
.empty)
(.branch 2238 34602
.empty
.empty))))
(.branch 2248 34741
(.branch 2244 10265
(.branch 2242 10217
(.branch 2241 34649
(.branch 2240 10341
.empty
.empty)
.empty)
(.branch 2243 34677
.empty
.empty))
(.branch 2246 10293
(.branch 2245 34725
.empty
.empty)
(.branch 2247 34601
.empty
.empty)))
(.branch 2253 10357
(.branch 2251 10405
(.branch 2250 34585
(.branch 2249 10153
.empty
.empty)
.empty)
(.branch 2252 34537
.empty
.empty))
(.branch 2255 10201
(.branch 2254 34789
.empty
.empty)
(.branch 2256 10154
.empty
.empty)))))
(.branch 2275 34665
(.branch 2266 34666
(.branch 2262 10202
(.branch 2260 10358
(.branch 2259 34586
(.branch 2258 10406
.empty
.empty)
.empty)
(.branch 2261 34538
.empty
.empty))
(.branch 2264 34662
(.branch 2263 34790
.empty
.empty)
(.branch 2265 10330
.empty
.empty)))
(.branch 2271 10282
(.branch 2269 10278
(.branch 2268 34714
(.branch 2267 10230
.empty
.empty)
.empty)
(.branch 2270 34614
.empty
.empty))
(.branch 2273 34661
(.branch 2272 10329
.empty
.empty)
(.branch 2274 10229
.empty
.empty))))
(.branch 2284 147
(.branch 2280 1072
(.branch 2278 10281
(.branch 2277 34713
(.branch 2276 10277
.empty
.empty)
.empty)
(.branch 2279 34613
.empty
.empty))
(.branch 2282 422
(.branch 2281 1078
.empty
.empty)
(.branch 2283 95
.empty
.empty)))
(.branch 2288 1077
(.branch 2286 1120
(.branch 2285 372
.empty
.empty)
(.branch 2287 1126
.empty
.empty))
(.branch 2290 113
(.branch 2289 1068
.empty
.empty)
(.branch 2291 406
.empty
.empty)))))))))))
(.branch 3438 68547
(.branch 2865 64322
(.branch 2579 68576
(.branch 2436 34695
(.branch 2364 32986
(.branch 2328 404
(.branch 2310 112
(.branch 2301 1110
(.branch 2297 369
(.branch 2295 1116
(.branch 2294 1125
(.branch 2293 131
.empty
.empty)
.empty)
(.branch 2296 144
.empty
.empty))
(.branch 2299 1081
(.branch 2298 1087
.empty
.empty)
(.branch 2300 1104
.empty
.empty)))
(.branch 2306 1082
(.branch 2304 387
(.branch 2303 94
(.branch 2302 421
.empty
.empty)
.empty)
(.branch 2305 128
.empty
.empty))
(.branch 2308 1109
(.branch 2307 1091
.empty
.empty)
(.branch 2309 1100
.empty
.empty))))
(.branch 2319 1114
(.branch 2315 389
(.branch 2313 1066
(.branch 2312 1075
(.branch 2311 405
.empty
.empty)
.empty)
(.branch 2314 130
.empty
.empty))
(.branch 2317 114
(.branch 2316 407
.empty
.empty)
(.branch 2318 1123
.empty
.empty)))
(.branch 2324 96
(.branch 2322 371
(.branch 2321 1071
(.branch 2320 1065
.empty
.empty)
.empty)
(.branch 2323 146
.empty
.empty))
(.branch 2326 1113
(.branch 2325 423
.empty
.empty)
(.branch 2327 1119
.empty
.empty)))))
(.branch 2346 32997
(.branch 2337 420
(.branch 2333 1098
(.branch 2331 1093
(.branch 2330 1084
(.branch 2329 111
.empty
.empty)
.empty)
(.branch 2332 1107
.empty
.empty))
(.branch 2335 388
(.branch 2334 129
.empty
.empty)
(.branch 2336 93
.empty
.empty)))
(.branch 2342 370
(.branch 2340 1097
(.branch 2339 1088
(.branch 2338 1094
.empty
.empty)
.empty)
(.branch 2341 1103
.empty
.empty))
(.branch 2344 32965
(.branch 2343 145
.empty
.empty)
(.branch 2345 53
.empty
.empty))))
(.branch 2355 32998
(.branch 2351 328
(.branch 2349 51
(.branch 2348 32949
(.branch 2347 326
.empty
.empty)
.empty)
(.branch 2350 32970
.empty
.empty))
(.branch 2353 32966
(.branch 2352 73
.empty
.empty)
(.branch 2354 346
.empty
.empty)))
(.branch 2360 32981
(.branch 2358 348
(.branch 2357 32950
(.branch 2356 71
.empty
.empty)
.empty)
(.branch 2359 32969
.empty
.empty))
(.branch 2362 32938
(.branch 2361 52
.empty
.empty)
(.branch 2363 327
.empty
.empty))))))
(.branch 2400 32979
(.branch 2382 285
(.branch 2373 32985
(.branch 2369 32982
(.branch 2367 329
(.branch 2366 32954
(.branch 2365 50
.empty
.empty)
.empty)
(.branch 2368 72
.empty
.empty))
(.branch 2371 32937
(.branch 2370 347
.empty
.empty)
(.branch 2372 70
.empty
.empty)))
(.branch 2378 283
(.branch 2376 10
(.branch 2375 32953
(.branch 2374 349
.empty
.empty)
.empty)
(.branch 2377 32959
.empty
.empty))
(.branch 2380 8
(.branch 2379 32991
.empty
.empty)
(.branch 2381 32943
.empty
.empty))))
(.branch 2391 307
(.branch 2387 305
(.branch 2385 32
(.branch 2384 32963
(.branch 2383 32976
.empty
.empty)
.empty)
(.branch 2386 32995
.empty
.empty))
(.branch 2389 30
(.branch 2388 32947
.empty
.empty)
(.branch 2390 32972
.empty
.empty)))
(.branch 2396 7
(.branch 2394 284
(.branch 2393 32975
(.branch 2392 9
.empty
.empty)
.empty)
(.branch 2395 32944
.empty
.empty))
(.branch 2398 286
(.branch 2397 32992
.empty
.empty)
(.branch 2399 32960
.empty
.empty)))))
(.branch 2418 10187
(.branch 2409 10388
(.branch 2405 29
(.branch 2403 306
(.branch 2402 32940
(.branch 2401 31
.empty
.empty)
.empty)
(.branch 2404 32988
.empty
.empty))
(.branch 2407 308
(.branch 2406 32956
.empty
.empty)
(.branch 2408 10363
.empty
.empty)))
(.branch 2414 34763
(.branch 2412 34683
(.branch 2411 10308
(.branch 2410 10315
.empty
.empty)
.empty)
(.branch 2413 34708
.empty
.empty))
(.branch 2416 10235
(.branch 2415 34756
.empty
.empty)
(.branch 2417 10260
.empty
.empty))))
(.branch 2427 10168
(.branch 2423 34628
(.branch 2421 34580
(.branch 2420 34555
(.branch 2419 10180
.empty
.empty)
.empty)
(.branch 2422 34635
.empty
.empty))
(.branch 2425 10248
(.branch 2424 10247
.empty
.empty)
(.branch 2426 10199
.empty
.empty)))
(.branch 2432 10375
(.branch 2430 34647
(.branch 2429 34568
(.branch 2428 34567
.empty
.empty)
.empty)
(.branch 2431 34616
.empty
.empty))
(.branch 2434 10327
(.branch 2433 10376
.empty
.empty)
(.branch 2435 10296
.empty
.empty)))))))
(.branch 2508 10290
(.branch 2472 34609
(.branch 2454 34571
(.branch 2445 34772
(.branch 2441 10324
(.branch 2439 34744
(.branch 2438 34775
(.branch 2437 34696
.empty
.empty)
.empty)
(.branch 2440 10299
.empty
.empty))
(.branch 2443 10372
(.branch 2442 10379
.empty
.empty)
(.branch 2444 34747
.empty
.empty)))
(.branch 2450 10251
(.branch 2448 10171
(.branch 2447 34692
(.branch 2446 34699
.empty
.empty)
.empty)
(.branch 2449 10196
.empty
.empty))
(.branch 2452 34619
(.branch 2451 10244
.empty
.empty)
(.branch 2453 34644
.empty
.empty))))
(.branch 2463 34552
(.branch 2459 10232
(.branch 2457 10184
(.branch 2456 10183
(.branch 2455 34564
.empty
.empty)
.empty)
(.branch 2458 10263
.empty
.empty))
(.branch 2461 34632
(.branch 2460 34631
.empty
.empty)
(.branch 2462 34583
.empty
.empty)))
(.branch 2468 34759
(.branch 2466 10391
(.branch 2465 10312
(.branch 2464 10311
.empty
.empty)
.empty)
(.branch 2467 10360
.empty
.empty))
(.branch 2470 34711
(.branch 2469 34760
.empty
.empty)
(.branch 2471 34680
.empty
.empty)))))
(.branch 2490 34657
(.branch 2481 10206
(.branch 2477 10289
(.branch 2475 10273
(.branch 2474 34593
(.branch 2473 10161
.empty
.empty)
.empty)
(.branch 2476 34737
.empty
.empty))
(.branch 2479 10401
(.branch 2478 34721
.empty
.empty)
(.branch 2480 34654
.empty
.empty)))
(.branch 2486 34670
(.branch 2484 34782
(.branch 2483 10222
(.branch 2482 34542
.empty
.empty)
.empty)
(.branch 2485 10334
.empty
.empty))
(.branch 2488 34545
(.branch 2487 10350
.empty
.empty)
(.branch 2489 10225
.empty
.empty))))
(.branch 2499 10158
(.branch 2495 10337
(.branch 2493 10353
(.branch 2492 34673
(.branch 2491 10209
.empty
.empty)
.empty)
(.branch 2494 34785
.empty
.empty))
(.branch 2497 10270
(.branch 2496 34590
.empty
.empty)
(.branch 2498 34606
.empty
.empty)))
(.branch 2504 10162
(.branch 2502 34734
(.branch 2501 10398
(.branch 2500 34718
.empty
.empty)
.empty)
(.branch 2503 10286
.empty
.empty))
(.branch 2506 10274
(.branch 2505 34610
.empty
.empty)
(.branch 2507 34594
.empty
.empty))))))
(.branch 2544 68482
(.branch 2526 10338
(.branch 2517 34781
(.branch 2513 34653
(.branch 2511 34722
(.branch 2510 10402
(.branch 2509 34738
.empty
.empty)
.empty)
(.branch 2512 10205
.empty
.empty))
(.branch 2515 34541
(.branch 2514 10221
.empty
.empty)
(.branch 2516 10333
.empty
.empty)))
(.branch 2522 10210
(.branch 2520 10226
(.branch 2519 34669
(.branch 2518 10349
.empty
.empty)
.empty)
(.branch 2521 34546
.empty
.empty))
(.branch 2524 10354
(.branch 2523 34658
.empty
.empty)
(.branch 2525 34674
.empty
.empty))))
(.branch 2535 34733
(.branch 2531 34605
(.branch 2529 34589
(.branch 2528 10269
(.branch 2527 34786
.empty
.empty)
.empty)
(.branch 2530 10157
.empty
.empty))
(.branch 2533 34717
(.branch 2532 10397
.empty
.empty)
(.branch 2534 10285
.empty
.empty)))
(.branch 2540 68578
(.branch 2538 68408
(.branch 2537 68386
(.branch 2536 68650
.empty
.empty)
.empty)
(.branch 2539 68624
.empty
.empty))
(.branch 2542 68432
(.branch 2541 68458
.empty
.empty)
(.branch 2543 68600
.empty
.empty)))))
(.branch 2562 68483
(.branch 2553 68625
(.branch 2549 68674
(.branch 2547 68504
(.branch 2546 68528
(.branch 2545 68554
.empty
.empty)
.empty)
(.branch 2548 68362
.empty
.empty))
(.branch 2551 68336
(.branch 2550 68696
.empty
.empty)
(.branch 2552 68409
.empty
.empty)))
(.branch 2558 68579
(.branch 2556 68433
(.branch 2555 68387
(.branch 2554 68651
.empty
.empty)
.empty)
(.branch 2557 68601
.empty
.empty))
(.branch 2560 68529
(.branch 2559 68459
.empty
.empty)
(.branch 2561 68505
.empty
.empty))))
(.branch 2571 68360
(.branch 2567 68675
(.branch 2565 68337
(.branch 2564 68697
(.branch 2563 68555
.empty
.empty)
.empty)
(.branch 2566 68363
.empty
.empty))
(.branch 2569 68698
(.branch 2568 68338
.empty
.empty)
(.branch 2570 68672
.empty
.empty)))
(.branch 2575 68480
(.branch 2573 68530
(.branch 2572 68506
.empty
.empty)
(.branch 2574 68552
.empty
.empty))
(.branch 2577 68434
(.branch 2576 68602
.empty
.empty)
(.branch 2578 68456
.empty
.empty))))))))
(.branch 2722 54322
(.branch 2651 68699
(.branch 2615 68336
(.branch 2597 68649
(.branch 2588 68553
(.branch 2584 68673
(.branch 2582 68384
(.branch 2581 68410
(.branch 2580 68626
.empty
.empty)
.empty)
(.branch 2583 68648
.empty
.empty))
(.branch 2586 68339
(.branch 2585 68361
.empty
.empty)
(.branch 2587 68699
.empty
.empty)))
(.branch 2593 68577
(.branch 2591 68531
(.branch 2590 68507
(.branch 2589 68481
.empty
.empty)
.empty)
(.branch 2592 68457
.empty
.empty))
(.branch 2595 68435
(.branch 2594 68603
.empty
.empty)
(.branch 2596 68385
.empty
.empty))))
(.branch 2606 68432
(.branch 2602 68408
(.branch 2600 68650
(.branch 2599 68411
(.branch 2598 68627
.empty
.empty)
.empty)
(.branch 2601 68386
.empty
.empty))
(.branch 2604 68578
(.branch 2603 68624
.empty
.empty)
(.branch 2605 68458
.empty
.empty)))
(.branch 2611 68504
(.branch 2609 68554
(.branch 2608 68482
(.branch 2607 68600
.empty
.empty)
.empty)
(.branch 2610 68528
.empty
.empty))
(.branch 2613 68674
(.branch 2612 68362
.empty
.empty)
(.branch 2614 68696
.empty
.empty)))))
(.branch 2633 68698
(.branch 2624 68529
(.branch 2620 68433
(.branch 2618 68651
(.branch 2617 68625
(.branch 2616 68409
.empty
.empty)
.empty)
(.branch 2619 68387
.empty
.empty))
(.branch 2622 68579
(.branch 2621 68601
.empty
.empty)
(.branch 2623 68459
.empty
.empty)))
(.branch 2629 68337
(.branch 2627 68555
(.branch 2626 68483
(.branch 2625 68505
.empty
.empty)
.empty)
(.branch 2628 68697
.empty
.empty))
(.branch 2631 68675
(.branch 2630 68363
.empty
.empty)
(.branch 2632 68338
.empty
.empty))))
(.branch 2642 68456
(.branch 2638 68552
(.branch 2636 68506
(.branch 2635 68360
(.branch 2634 68672
.empty
.empty)
.empty)
(.branch 2637 68530
.empty
.empty))
(.branch 2640 68602
(.branch 2639 68480
.empty
.empty)
(.branch 2641 68434
.empty
.empty)))
(.branch 2647 68648
(.branch 2645 68410
(.branch 2644 68626
(.branch 2643 68576
.empty
.empty)
.empty)
(.branch 2646 68384
.empty
.empty))
(.branch 2649 68361
(.branch 2648 68673
.empty
.empty)
(.branch 2650 68339
.empty
.empty))))))
(.branch 2687 54224
(.branch 2669 54344
(.branch 2660 68385
(.branch 2656 68457
(.branch 2654 68507
(.branch 2653 68481
(.branch 2652 68553
.empty
.empty)
.empty)
(.branch 2655 68531
.empty
.empty))
(.branch 2658 68603
(.branch 2657 68577
.empty
.empty)
(.branch 2659 68435
.empty
.empty)))
(.branch 2665 54130
(.branch 2663 68411
(.branch 2662 68627
(.branch 2661 68649
.empty
.empty)
.empty)
(.branch 2664 54129
.empty
.empty))
(.branch 2667 54464
(.branch 2666 54467
.empty
.empty)
(.branch 2668 54347
.empty
.empty))))
(.branch 2678 54179
(.branch 2674 54393
(.branch 2672 54251
(.branch 2671 54298
(.branch 2670 54297
.empty
.empty)
.empty)
(.branch 2673 54248
.empty
.empty))
(.branch 2676 54417
(.branch 2675 54394
.empty
.empty)
(.branch 2677 54418
.empty
.empty)))
(.branch 2683 54442
(.branch 2681 54200
(.branch 2680 54203
(.branch 2679 54176
.empty
.empty)
.empty)
(.branch 2682 54441
.empty
.empty))
(.branch 2685 54370
(.branch 2684 54369
.empty
.empty)
(.branch 2686 54227
.empty
.empty)))))
(.branch 2705 54249
(.branch 2696 54128
(.branch 2692 54491
(.branch 2690 54323
(.branch 2689 54274
(.branch 2688 54273
.empty
.empty)
.empty)
(.branch 2691 54320
.empty
.empty))
(.branch 2694 54153
(.branch 2693 54488
.empty
.empty)
(.branch 2695 54154
.empty
.empty)))
(.branch 2701 54345
(.branch 2699 54465
(.branch 2698 54466
(.branch 2697 54131
.empty
.empty)
.empty)
(.branch 2700 54346
.empty
.empty))
(.branch 2703 54299
(.branch 2702 54296
.empty
.empty)
(.branch 2704 54250
.empty
.empty))))
(.branch 2714 54440
(.branch 2710 54178
(.branch 2708 54416
(.branch 2707 54395
(.branch 2706 54392
.empty
.empty)
.empty)
(.branch 2709 54419
.empty
.empty))
(.branch 2712 54202
(.branch 2711 54177
.empty
.empty)
(.branch 2713 54201
.empty
.empty)))
(.branch 2718 54226
(.branch 2716 54368
(.branch 2715 54443
.empty
.empty)
(.branch 2717 54371
.empty
.empty))
(.branch 2720 54272
(.branch 2719 54225
.empty
.empty)
(.branch 2721 54275
.empty
.empty)))))))
(.branch 2794 64443
(.branch 2758 54153
(.branch 2740 54417
(.branch 2731 54464
(.branch 2727 54155
(.branch 2725 54489
(.branch 2724 54490
(.branch 2723 54321
.empty
.empty)
.empty)
(.branch 2726 54152
.empty
.empty))
(.branch 2729 54130
(.branch 2728 54129
.empty
.empty)
(.branch 2730 54467
.empty
.empty)))
(.branch 2736 54251
(.branch 2734 54297
(.branch 2733 54344
(.branch 2732 54347
.empty
.empty)
.empty)
(.branch 2735 54298
.empty
.empty))
(.branch 2738 54393
(.branch 2737 54248
.empty
.empty)
(.branch 2739 54394
.empty
.empty))))
(.branch 2749 54370
(.branch 2745 54200
(.branch 2743 54176
(.branch 2742 54179
(.branch 2741 54418
.empty
.empty)
.empty)
(.branch 2744 54203
.empty
.empty))
(.branch 2747 54442
(.branch 2746 54441
.empty
.empty)
(.branch 2748 54369
.empty
.empty)))
(.branch 2754 54323
(.branch 2752 54273
(.branch 2751 54224
(.branch 2750 54227
.empty
.empty)
.empty)
(.branch 2753 54274
.empty
.empty))
(.branch 2756 54491
(.branch 2755 54320
.empty
.empty)
(.branch 2757 54488
.empty
.empty)))))
(.branch 2776 54202
(.branch 2767 54299
(.branch 2763 54465
(.branch 2761 54131
(.branch 2760 54128
(.branch 2759 54154
.empty
.empty)
.empty)
(.branch 2762 54466
.empty
.empty))
(.branch 2765 54345
(.branch 2764 54346
.empty
.empty)
(.branch 2766 54296
.empty
.empty)))
(.branch 2772 54416
(.branch 2770 54392
(.branch 2769 54249
(.branch 2768 54250
.empty
.empty)
.empty)
(.branch 2771 54395
.empty
.empty))
(.branch 2774 54178
(.branch 2773 54419
.empty
.empty)
(.branch 2775 54177
.empty
.empty))))
(.branch 2785 54275
(.branch 2781 54371
(.branch 2779 54443
(.branch 2778 54440
(.branch 2777 54201
.empty
.empty)
.empty)
(.branch 2780 54368
.empty
.empty))
(.branch 2783 54225
(.branch 2782 54226
.empty
.empty)
(.branch 2784 54272
.empty
.empty)))
(.branch 2790 54152
(.branch 2788 54490
(.branch 2787 54321
(.branch 2786 54322
.empty
.empty)
.empty)
(.branch 2789 54489
.empty
.empty))
(.branch 2792 64419
(.branch 2791 54155
.empty
.empty)
(.branch 2793 64394
.empty
.empty))))))
(.branch 2830 64323
(.branch 2812 64224
(.branch 2803 64346
(.branch 2799 64250
(.branch 2797 64226
(.branch 2796 64203
(.branch 2795 64466
.empty
.empty)
.empty)
(.branch 2798 64275
.empty
.empty))
(.branch 2801 64322
(.branch 2800 64299
.empty
.empty)
(.branch 2802 64371
.empty
.empty)))
(.branch 2808 64392
(.branch 2806 64155
(.branch 2805 64106
(.branch 2804 64131
.empty
.empty)
.empty)
(.branch 2807 64178
.empty
.empty))
(.branch 2810 64464
(.branch 2809 64417
.empty
.empty)
(.branch 2811 64441
.empty
.empty))))
(.branch 2821 64129
(.branch 2817 64297
(.branch 2815 64273
(.branch 2814 64248
(.branch 2813 64201
.empty
.empty)
.empty)
(.branch 2816 64320
.empty
.empty))
(.branch 2819 64369
(.branch 2818 64344
.empty
.empty)
(.branch 2820 64104
.empty
.empty)))
(.branch 2826 64107
(.branch 2824 64179
(.branch 2823 64153
(.branch 2822 64176
.empty
.empty)
.empty)
(.branch 2825 64154
.empty
.empty))
(.branch 2828 64347
(.branch 2827 64130
.empty
.empty)
(.branch 2829 64370
.empty
.empty)))))
(.branch 2848 64272
(.branch 2839 64418
(.branch 2835 64202
(.branch 2833 64274
(.branch 2832 64251
(.branch 2831 64298
.empty
.empty)
.empty)
(.branch 2834 64227
.empty
.empty))
(.branch 2837 64442
(.branch 2836 64467
.empty
.empty)
(.branch 2838 64395
.empty
.empty)))
(.branch 2844 64368
(.branch 2842 64128
(.branch 2841 64177
(.branch 2840 64152
.empty
.empty)
.empty)
(.branch 2843 64105
.empty
.empty))
(.branch 2846 64296
(.branch 2845 64345
.empty
.empty)
(.branch 2847 64321
.empty
.empty))))
(.branch 2857 64394
(.branch 2853 64465
(.branch 2851 64225
(.branch 2850 64200
(.branch 2849 64249
.empty
.empty)
.empty)
(.branch 2852 64440
.empty
.empty))
(.branch 2855 64393
(.branch 2854 64416
.empty
.empty)
(.branch 2856 64419
.empty
.empty)))
(.branch 2861 64226
(.branch 2859 64466
(.branch 2858 64443
.empty
.empty)
(.branch 2860 64203
.empty
.empty))
(.branch 2863 64250
(.branch 2862 64275
.empty
.empty)
(.branch 2864 64299
.empty
.empty)))))))))
(.branch 3152 58424
(.branch 3009 58585
(.branch 2937 58633
(.branch 2901 64442
(.branch 2883 64369
(.branch 2874 64464
(.branch 2870 64155
(.branch 2868 64131
(.branch 2867 64346
(.branch 2866 64371
.empty
.empty)
.empty)
(.branch 2869 64106
.empty
.empty))
(.branch 2872 64392
(.branch 2871 64178
.empty
.empty)
(.branch 2873 64417
.empty
.empty)))
(.branch 2879 64273
(.branch 2877 64201
(.branch 2876 64224
(.branch 2875 64441
.empty
.empty)
.empty)
(.branch 2878 64248
.empty
.empty))
(.branch 2881 64297
(.branch 2880 64320
.empty
.empty)
(.branch 2882 64344
.empty
.empty))))
(.branch 2892 64347
(.branch 2888 64179
(.branch 2886 64176
(.branch 2885 64129
(.branch 2884 64104
.empty
.empty)
.empty)
(.branch 2887 64153
.empty
.empty))
(.branch 2890 64107
(.branch 2889 64154
.empty
.empty)
(.branch 2891 64130
.empty
.empty)))
(.branch 2897 64274
(.branch 2895 64298
(.branch 2894 64323
(.branch 2893 64370
.empty
.empty)
.empty)
(.branch 2896 64251
.empty
.empty))
(.branch 2899 64202
(.branch 2898 64227
.empty
.empty)
(.branch 2900 64467
.empty
.empty)))))
(.branch 2919 64393
(.branch 2910 64296
(.branch 2906 64128
(.branch 2904 64152
(.branch 2903 64418
(.branch 2902 64395
.empty
.empty)
.empty)
(.branch 2905 64177
.empty
.empty))
(.branch 2908 64368
(.branch 2907 64105
.empty
.empty)
(.branch 2909 64345
.empty
.empty)))
(.branch 2915 64225
(.branch 2913 64249
(.branch 2912 64272
(.branch 2911 64321
.empty
.empty)
.empty)
(.branch 2914 64200
.empty
.empty))
(.branch 2917 64465
(.branch 2916 64440
.empty
.empty)
(.branch 2918 64416
.empty
.empty))))
(.branch 2928 58584
(.branch 2924 58488
(.branch 2922 58704
(.branch 2921 58682
(.branch 2920 58632
.empty
.empty)
.empty)
(.branch 2923 58658
.empty
.empty))
(.branch 2926 58464
(.branch 2925 58442
.empty
.empty)
(.branch 2927 58514
.empty
.empty)))
(.branch 2933 58394
(.branch 2931 58610
(.branch 2930 58560
(.branch 2929 58538
.empty
.empty)
.empty)
(.branch 2932 58344
.empty
.empty))
(.branch 2935 58370
(.branch 2934 58416
.empty
.empty)
(.branch 2936 58683
.empty
.empty))))))
(.branch 2973 58609
(.branch 2955 58346
(.branch 2946 58611
(.branch 2942 58515
(.branch 2940 58443
(.branch 2939 58705
(.branch 2938 58659
.empty
.empty)
.empty)
(.branch 2941 58489
.empty
.empty))
(.branch 2944 58539
(.branch 2943 58465
.empty
.empty)
(.branch 2945 58585
.empty
.empty)))
(.branch 2951 58417
(.branch 2949 58345
(.branch 2948 58395
(.branch 2947 58561
.empty
.empty)
.empty)
(.branch 2950 58371
.empty
.empty))
(.branch 2953 58418
(.branch 2952 58368
.empty
.empty)
(.branch 2954 58392
.empty
.empty))))
(.branch 2964 58656
(.branch 2960 58512
(.branch 2958 58536
(.branch 2957 58562
(.branch 2956 58608
.empty
.empty)
.empty)
(.branch 2959 58586
.empty
.empty))
(.branch 2962 58440
(.branch 2961 58466
.empty
.empty)
(.branch 2963 58490
.empty
.empty)))
(.branch 2969 58369
(.branch 2967 58634
(.branch 2966 58680
(.branch 2965 58706
.empty
.empty)
.empty)
(.branch 2968 58419
.empty
.empty))
(.branch 2971 58393
(.branch 2970 58347
.empty
.empty)
(.branch 2972 58563
.empty
.empty)))))
(.branch 2991 58514
(.branch 2982 58635
(.branch 2978 58491
(.branch 2976 58467
(.branch 2975 58537
(.branch 2974 58587
.empty
.empty)
.empty)
(.branch 2977 58513
.empty
.empty))
(.branch 2980 58707
(.branch 2979 58441
.empty
.empty)
(.branch 2981 58657
.empty
.empty)))
(.branch 2987 58658
(.branch 2985 58682
(.branch 2984 58632
(.branch 2983 58681
.empty
.empty)
.empty)
(.branch 2986 58704
.empty
.empty))
(.branch 2989 58442
(.branch 2988 58488
.empty
.empty)
(.branch 2990 58464
.empty
.empty))))
(.branch 3000 58683
(.branch 2996 58344
(.branch 2994 58560
(.branch 2993 58538
(.branch 2992 58584
.empty
.empty)
.empty)
(.branch 2995 58610
.empty
.empty))
(.branch 2998 58416
(.branch 2997 58394
.empty
.empty)
(.branch 2999 58370
.empty
.empty)))
(.branch 3005 58489
(.branch 3003 58705
(.branch 3002 58659
(.branch 3001 58633
.empty
.empty)
.empty)
(.branch 3004 58443
.empty
.empty))
(.branch 3007 58465
(.branch 3006 58515
.empty
.empty)
(.branch 3008 58539
.empty
.empty)))))))
(.branch 3081 58448
(.branch 3045 58657
(.branch 3027 58490
(.branch 3018 58392
(.branch 3014 58371
(.branch 3012 58395
(.branch 3011 58561
(.branch 3010 58611
.empty
.empty)
.empty)
(.branch 3013 58345
.empty
.empty))
(.branch 3016 58368
(.branch 3015 58417
.empty
.empty)
(.branch 3017 58418
.empty
.empty)))
(.branch 3023 58586
(.branch 3021 58562
(.branch 3020 58608
(.branch 3019 58346
.empty
.empty)
.empty)
(.branch 3022 58536
.empty
.empty))
(.branch 3025 58466
(.branch 3024 58512
.empty
.empty)
(.branch 3026 58440
.empty
.empty))))
(.branch 3036 58563
(.branch 3032 58419
(.branch 3030 58680
(.branch 3029 58706
(.branch 3028 58656
.empty
.empty)
.empty)
(.branch 3031 58634
.empty
.empty))
(.branch 3034 58347
(.branch 3033 58369
.empty
.empty)
(.branch 3035 58393
.empty
.empty)))
(.branch 3041 58513
(.branch 3039 58537
(.branch 3038 58587
(.branch 3037 58609
.empty
.empty)
.empty)
(.branch 3040 58467
.empty
.empty))
(.branch 3043 58441
(.branch 3042 58491
.empty
.empty)
(.branch 3044 58707
.empty
.empty)))))
(.branch 3063 58689
(.branch 3054 58569
(.branch 3050 58571
(.branch 3048 58640
(.branch 3047 58681
(.branch 3046 58635
.empty
.empty)
.empty)
(.branch 3049 58475
.empty
.empty))
(.branch 3052 58642
(.branch 3051 58352
.empty
.empty)
(.branch 3053 58473
.empty
.empty)))
(.branch 3059 58691
(.branch 3057 58616
(.branch 3056 58403
(.branch 3055 58354
.empty
.empty)
.empty)
(.branch 3058 58520
.empty
.empty))
(.branch 3061 58618
(.branch 3060 58401
.empty
.empty)
(.branch 3062 58522
.empty
.empty))))
(.branch 3072 58402
(.branch 3068 58643
(.branch 3066 58570
(.branch 3065 58474
(.branch 3064 58641
.empty
.empty)
.empty)
(.branch 3067 58353
.empty
.empty))
(.branch 3070 58568
(.branch 3069 58472
.empty
.empty)
(.branch 3071 58355
.empty
.empty)))
(.branch 3077 58619
(.branch 3075 58690
(.branch 3074 58521
(.branch 3073 58617
.empty
.empty)
.empty)
(.branch 3076 58400
.empty
.empty))
(.branch 3079 58688
(.branch 3078 58523
.empty
.empty)
(.branch 3080 58667
.empty
.empty))))))
(.branch 3117 58473
(.branch 3099 58378
(.branch 3090 58499
(.branch 3086 58546
(.branch 3084 58665
(.branch 3083 58379
(.branch 3082 58544
.empty
.empty)
.empty)
(.branch 3085 58450
.empty
.empty))
(.branch 3088 58424
(.branch 3087 58377
.empty
.empty)
(.branch 3089 58595
.empty
.empty)))
(.branch 3095 58714
(.branch 3093 58593
(.branch 3092 58426
(.branch 3091 58712
.empty
.empty)
.empty)
(.branch 3094 58497
.empty
.empty))
(.branch 3097 58449
(.branch 3096 58666
.empty
.empty)
(.branch 3098 58545
.empty
.empty))))
(.branch 3108 58427
(.branch 3104 58425
(.branch 3102 58547
(.branch 3101 58451
(.branch 3100 58664
.empty
.empty)
.empty)
(.branch 3103 58376
.empty
.empty))
(.branch 3106 58498
(.branch 3105 58594
.empty
.empty)
(.branch 3107 58713
.empty
.empty)))
(.branch 3113 58475
(.branch 3111 58715
(.branch 3110 58496
(.branch 3109 58592
.empty
.empty)
.empty)
(.branch 3112 58640
.empty
.empty))
(.branch 3115 58352
(.branch 3114 58571
.empty
.empty)
(.branch 3116 58642
.empty
.empty)))))
(.branch 3135 58355
(.branch 3126 58522
(.branch 3122 58520
(.branch 3120 58403
(.branch 3119 58354
(.branch 3118 58569
.empty
.empty)
.empty)
(.branch 3121 58616
.empty
.empty))
(.branch 3124 58401
(.branch 3123 58691
.empty
.empty)
(.branch 3125 58618
.empty
.empty)))
(.branch 3131 58353
(.branch 3129 58474
(.branch 3128 58641
(.branch 3127 58689
.empty
.empty)
.empty)
(.branch 3130 58570
.empty
.empty))
(.branch 3133 58472
(.branch 3132 58643
.empty
.empty)
(.branch 3134 58568
.empty
.empty))))
(.branch 3144 58667
(.branch 3140 58400
(.branch 3138 58521
(.branch 3137 58617
(.branch 3136 58402
.empty
.empty)
.empty)
(.branch 3139 58690
.empty
.empty))
(.branch 3142 58523
(.branch 3141 58619
.empty
.empty)
(.branch 3143 58688
.empty
.empty)))
(.branch 3148 58665
(.branch 3146 58544
(.branch 3145 58448
.empty
.empty)
(.branch 3147 58379
.empty
.empty))
(.branch 3150 58546
(.branch 3149 58450
.empty
.empty)
(.branch 3151 58377
.empty
.empty))))))))
(.branch 3295 64259
(.branch 3224 64401
(.branch 3188 64139
(.branch 3170 58498
(.branch 3161 58449
(.branch 3157 58593
(.branch 3155 58712
(.branch 3154 58499
(.branch 3153 58595
.empty
.empty)
.empty)
(.branch 3156 58426
.empty
.empty))
(.branch 3159 58714
(.branch 3158 58497
.empty
.empty)
(.branch 3160 58666
.empty
.empty)))
(.branch 3166 58547
(.branch 3164 58664
(.branch 3163 58378
(.branch 3162 58545
.empty
.empty)
.empty)
(.branch 3165 58451
.empty
.empty))
(.branch 3168 58425
(.branch 3167 58376
.empty
.empty)
(.branch 3169 58594
.empty
.empty))))
(.branch 3179 64448
(.branch 3175 58715
(.branch 3173 58592
(.branch 3172 58427
(.branch 3171 58713
.empty
.empty)
.empty)
(.branch 3174 58496
.empty
.empty))
(.branch 3177 64425
(.branch 3176 64427
.empty
.empty)
(.branch 3178 64450
.empty
.empty)))
(.branch 3184 64306
(.branch 3182 64283
(.branch 3181 64208
(.branch 3180 64210
.empty
.empty)
.empty)
(.branch 3183 64281
.empty
.empty))
(.branch 3186 64379
(.branch 3185 64304
.empty
.empty)
(.branch 3187 64377
.empty
.empty)))))
(.branch 3206 64161
(.branch 3197 64211
(.branch 3193 64426
(.branch 3191 64160
(.branch 3190 64162
(.branch 3189 64137
.empty
.empty)
.empty)
(.branch 3192 64424
.empty
.empty))
(.branch 3195 64451
(.branch 3194 64449
.empty
.empty)
(.branch 3196 64209
.empty
.empty)))
(.branch 3202 64376
(.branch 3200 64305
(.branch 3199 64282
(.branch 3198 64280
.empty
.empty)
.empty)
(.branch 3201 64307
.empty
.empty))
(.branch 3204 64136
(.branch 3203 64378
.empty
.empty)
(.branch 3205 64138
.empty
.empty))))
(.branch 3215 64256
(.branch 3211 64473
(.branch 3209 64400
(.branch 3208 64402
(.branch 3207 64163
.empty
.empty)
.empty)
(.branch 3210 64475
.empty
.empty))
(.branch 3213 64233
(.branch 3212 64235
.empty
.empty)
(.branch 3214 64258
.empty
.empty)))
(.branch 3220 64114
(.branch 3218 64354
(.branch 3217 64329
(.branch 3216 64331
.empty
.empty)
.empty)
(.branch 3219 64352
.empty
.empty))
(.branch 3222 64187
(.branch 3221 64112
.empty
.empty)
(.branch 3223 64185
.empty
.empty))))))
(.branch 3260 64209
(.branch 3242 64450
(.branch 3233 64330
(.branch 3229 64234
(.branch 3227 64474
(.branch 3226 64472
(.branch 3225 64403
.empty
.empty)
.empty)
(.branch 3228 64232
.empty
.empty))
(.branch 3231 64259
(.branch 3230 64257
.empty
.empty)
(.branch 3232 64328
.empty
.empty)))
(.branch 3238 64184
(.branch 3236 64113
(.branch 3235 64355
(.branch 3234 64353
.empty
.empty)
.empty)
(.branch 3237 64115
.empty
.empty))
(.branch 3240 64427
(.branch 3239 64186
.empty
.empty)
(.branch 3241 64425
.empty
.empty))))
(.branch 3251 64377
(.branch 3247 64281
(.branch 3245 64208
(.branch 3244 64210
(.branch 3243 64448
.empty
.empty)
.empty)
(.branch 3246 64283
.empty
.empty))
(.branch 3249 64304
(.branch 3248 64306
.empty
.empty)
(.branch 3250 64379
.empty
.empty)))
(.branch 3256 64424
(.branch 3254 64162
(.branch 3253 64137
(.branch 3252 64139
.empty
.empty)
.empty)
(.branch 3255 64160
.empty
.empty))
(.branch 3258 64449
(.branch 3257 64426
.empty
.empty)
(.branch 3259 64451
.empty
.empty)))))
(.branch 3278 64258
(.branch 3269 64138
(.branch 3265 64307
(.branch 3263 64282
(.branch 3262 64280
(.branch 3261 64211
.empty
.empty)
.empty)
(.branch 3264 64305
.empty
.empty))
(.branch 3267 64378
(.branch 3266 64376
.empty
.empty)
(.branch 3268 64136
.empty
.empty)))
(.branch 3274 64475
(.branch 3272 64402
(.branch 3271 64163
(.branch 3270 64161
.empty
.empty)
.empty)
(.branch 3273 64400
.empty
.empty))
(.branch 3276 64235
(.branch 3275 64473
.empty
.empty)
(.branch 3277 64233
.empty
.empty))))
(.branch 3287 64185
(.branch 3283 64352
(.branch 3281 64329
(.branch 3280 64331
(.branch 3279 64256
.empty
.empty)
.empty)
(.branch 3282 64354
.empty
.empty))
(.branch 3285 64112
(.branch 3284 64114
.empty
.empty)
(.branch 3286 64187
.empty
.empty)))
(.branch 3291 64474
(.branch 3289 64403
(.branch 3288 64401
.empty
.empty)
(.branch 3290 64472
.empty
.empty))
(.branch 3293 64234
(.branch 3292 64232
.empty
.empty)
(.branch 3294 64257
.empty
.empty)))))))
(.branch 3367 54168
(.branch 3331 54362
(.branch 3313 54218
(.branch 3304 54121
(.branch 3300 64113
(.branch 3298 64353
(.branch 3297 64330
(.branch 3296 64328
.empty
.empty)
.empty)
(.branch 3299 64355
.empty
.empty))
(.branch 3302 64184
(.branch 3301 64115
.empty
.empty)
(.branch 3303 64186
.empty
.empty)))
(.branch 3309 54314
(.branch 3307 54482
(.branch 3306 54433
(.branch 3305 54170
.empty
.empty)
.empty)
(.branch 3308 54361
.empty
.empty))
(.branch 3311 54242
(.branch 3310 54289
.empty
.empty)
(.branch 3312 54265
.empty
.empty))))
(.branch 3322 54457
(.branch 3318 54145
(.branch 3316 54409
(.branch 3315 54338
(.branch 3314 54385
.empty
.empty)
.empty)
(.branch 3317 54458
.empty
.empty))
(.branch 3320 54193
(.branch 3319 54194
.empty
.empty)
(.branch 3321 54146
.empty
.empty)))
(.branch 3327 54266
(.branch 3325 54386
(.branch 3324 54337
(.branch 3323 54410
.empty
.empty)
.empty)
(.branch 3326 54217
.empty
.empty))
(.branch 3329 54290
(.branch 3328 54241
.empty
.empty)
(.branch 3330 54313
.empty
.empty)))))
(.branch 3349 54408
(.branch 3340 54315
(.branch 3336 54171
(.branch 3334 54169
(.branch 3333 54434
(.branch 3332 54481
.empty
.empty)
.empty)
(.branch 3335 54122
.empty
.empty))
(.branch 3338 54483
(.branch 3337 54120
.empty
.empty)
(.branch 3339 54432
.empty
.empty)))
(.branch 3345 54264
(.branch 3343 54288
(.branch 3342 54243
(.branch 3341 54360
.empty
.empty)
.empty)
(.branch 3344 54219
.empty
.empty))
(.branch 3347 54384
(.branch 3346 54339
.empty
.empty)
(.branch 3348 54459
.empty
.empty))))
(.branch 3358 54267
(.branch 3354 54411
(.branch 3352 54147
(.branch 3351 54144
(.branch 3350 54195
.empty
.empty)
.empty)
(.branch 3353 54192
.empty
.empty))
(.branch 3356 54387
(.branch 3355 54456
.empty
.empty)
(.branch 3357 54336
.empty
.empty)))
(.branch 3363 54312
(.branch 3361 54240
(.branch 3360 54291
(.branch 3359 54216
.empty
.empty)
.empty)
(.branch 3362 54363
.empty
.empty))
(.branch 3365 54480
(.branch 3364 54435
.empty
.empty)
(.branch 3366 54123
.empty
.empty))))))
(.branch 3403 54432
(.branch 3385 54146
(.branch 3376 54265
(.branch 3372 54361
(.branch 3370 54433
(.branch 3369 54170
(.branch 3368 54121
.empty
.empty)
.empty)
(.branch 3371 54482
.empty
.empty))
(.branch 3374 54289
(.branch 3373 54314
.empty
.empty)
(.branch 3375 54242
.empty
.empty)))
(.branch 3381 54458
(.branch 3379 54338
(.branch 3378 54385
(.branch 3377 54218
.empty
.empty)
.empty)
(.branch 3380 54409
.empty
.empty))
(.branch 3383 54194
(.branch 3382 54145
.empty
.empty)
(.branch 3384 54193
.empty
.empty))))
(.branch 3394 54313
(.branch 3390 54217
(.branch 3388 54337
(.branch 3387 54410
(.branch 3386 54457
.empty
.empty)
.empty)
(.branch 3389 54386
.empty
.empty))
(.branch 3392 54241
(.branch 3391 54266
.empty
.empty)
(.branch 3393 54290
.empty
.empty)))
(.branch 3399 54122
(.branch 3397 54434
(.branch 3396 54481
(.branch 3395 54362
.empty
.empty)
.empty)
(.branch 3398 54169
.empty
.empty))
(.branch 3401 54120
(.branch 3400 54171
.empty
.empty)
(.branch 3402 54483
.empty
.empty)))))
(.branch 3421 54336
(.branch 3412 54459
(.branch 3408 54219
(.branch 3406 54243
(.branch 3405 54360
(.branch 3404 54315
.empty
.empty)
.empty)
(.branch 3407 54288
.empty
.empty))
(.branch 3410 54339
(.branch 3409 54264
.empty
.empty)
(.branch 3411 54384
.empty
.empty)))
(.branch 3417 54192
(.branch 3415 54144
(.branch 3414 54195
(.branch 3413 54408
.empty
.empty)
.empty)
(.branch 3416 54147
.empty
.empty))
(.branch 3419 54456
(.branch 3418 54411
.empty
.empty)
(.branch 3420 54387
.empty
.empty))))
(.branch 3430 54123
(.branch 3426 54363
(.branch 3424 54291
(.branch 3423 54216
(.branch 3422 54267
.empty
.empty)
.empty)
(.branch 3425 54240
.empty
.empty))
(.branch 3428 54435
(.branch 3427 54312
.empty
.empty)
(.branch 3429 54480
.empty
.empty)))
(.branch 3434 68474
(.branch 3432 68642
(.branch 3431 54168
.empty
.empty)
(.branch 3433 68570
.empty
.empty))
(.branch 3436 68379
(.branch 3435 68354
.empty
.empty)
(.branch 3437 68451
.empty
.empty))))))))))
(.branch 4011 54412
(.branch 3725 58548
(.branch 3582 64356
(.branch 3510 68427
(.branch 3474 68424
(.branch 3456 68666
(.branch 3447 68403
(.branch 3443 68618
(.branch 3441 68498
(.branch 3440 68330
(.branch 3439 68667
.empty
.empty)
.empty)
(.branch 3442 68594
.empty
.empty))
(.branch 3445 68523
(.branch 3444 68691
.empty
.empty)
(.branch 3446 68427
.empty
.empty)))
(.branch 3452 68619
(.branch 3450 68522
(.branch 3449 68426
(.branch 3448 68402
.empty
.empty)
.empty)
(.branch 3451 68690
.empty
.empty))
(.branch 3454 68499
(.branch 3453 68595
.empty
.empty)
(.branch 3455 68331
.empty
.empty))))
(.branch 3465 68448
(.branch 3461 68475
(.branch 3459 68378
(.branch 3458 68450
(.branch 3457 68546
.empty
.empty)
.empty)
(.branch 3460 68355
.empty
.empty))
(.branch 3463 68643
(.branch 3462 68571
.empty
.empty)
(.branch 3464 68376
.empty
.empty)))
(.branch 3470 68473
(.branch 3468 68641
(.branch 3467 68664
(.branch 3466 68544
.empty
.empty)
.empty)
(.branch 3469 68569
.empty
.empty))
(.branch 3472 68688
(.branch 3471 68353
.empty
.empty)
(.branch 3473 68520
.empty
.empty)))))
(.branch 3492 68665
(.branch 3483 68328
(.branch 3479 68617
(.branch 3477 68497
(.branch 3476 68329
(.branch 3475 68400
.empty
.empty)
.empty)
(.branch 3478 68593
.empty
.empty))
(.branch 3481 68592
(.branch 3480 68616
.empty
.empty)
(.branch 3482 68496
.empty
.empty)))
(.branch 3488 68352
(.branch 3486 68521
(.branch 3485 68425
(.branch 3484 68401
.empty
.empty)
.empty)
(.branch 3487 68689
.empty
.empty))
(.branch 3490 68568
(.branch 3489 68472
.empty
.empty)
(.branch 3491 68640
.empty
.empty))))
(.branch 3501 68451
(.branch 3497 68570
(.branch 3495 68377
(.branch 3494 68449
(.branch 3493 68545
.empty
.empty)
.empty)
(.branch 3496 68642
.empty
.empty))
(.branch 3499 68354
(.branch 3498 68474
.empty
.empty)
(.branch 3500 68379
.empty
.empty)))
(.branch 3506 68594
(.branch 3504 68330
(.branch 3503 68667
(.branch 3502 68547
.empty
.empty)
.empty)
(.branch 3505 68498
.empty
.empty))
(.branch 3508 68691
(.branch 3507 68618
.empty
.empty)
(.branch 3509 68523
.empty
.empty))))))
(.branch 3546 68496
(.branch 3528 68376
(.branch 3519 68331
(.branch 3515 68690
(.branch 3513 68426
(.branch 3512 68402
(.branch 3511 68403
.empty
.empty)
.empty)
(.branch 3514 68522
.empty
.empty))
(.branch 3517 68595
(.branch 3516 68619
.empty
.empty)
(.branch 3518 68499
.empty
.empty)))
(.branch 3524 68355
(.branch 3522 68450
(.branch 3521 68546
(.branch 3520 68666
.empty
.empty)
.empty)
(.branch 3523 68378
.empty
.empty))
(.branch 3526 68571
(.branch 3525 68475
.empty
.empty)
(.branch 3527 68643
.empty
.empty))))
(.branch 3537 68520
(.branch 3533 68569
(.branch 3531 68664
(.branch 3530 68544
(.branch 3529 68448
.empty
.empty)
.empty)
(.branch 3532 68641
.empty
.empty))
(.branch 3535 68353
(.branch 3534 68473
.empty
.empty)
(.branch 3536 68688
.empty
.empty)))
(.branch 3542 68593
(.branch 3540 68329
(.branch 3539 68400
(.branch 3538 68424
.empty
.empty)
.empty)
(.branch 3541 68497
.empty
.empty))
(.branch 3544 68616
(.branch 3543 68617
.empty
.empty)
(.branch 3545 68592
.empty
.empty)))))
(.branch 3564 64406
(.branch 3555 68640
(.branch 3551 68689
(.branch 3549 68425
(.branch 3548 68401
(.branch 3547 68328
.empty
.empty)
.empty)
(.branch 3550 68521
.empty
.empty))
(.branch 3553 68472
(.branch 3552 68352
.empty
.empty)
(.branch 3554 68568
.empty
.empty)))
(.branch 3560 64430
(.branch 3558 68449
(.branch 3557 68545
(.branch 3556 68665
.empty
.empty)
.empty)
(.branch 3559 68377
.empty
.empty))
(.branch 3562 64310
(.branch 3561 64214
.empty
.empty)
(.branch 3563 64142
.empty
.empty))))
(.branch 3573 64263
(.branch 3569 64287
(.branch 3567 64118
(.branch 3566 64334
(.branch 3565 64238
.empty
.empty)
.empty)
(.branch 3568 64455
.empty
.empty))
(.branch 3571 64167
(.branch 3570 64383
.empty
.empty)
(.branch 3572 64479
.empty
.empty)))
(.branch 3578 64380
(.branch 3576 64452
(.branch 3575 64191
(.branch 3574 64359
.empty
.empty)
.empty)
(.branch 3577 64284
.empty
.empty))
(.branch 3580 64476
(.branch 3579 64164
.empty
.empty)
(.branch 3581 64260
.empty
.empty)))))))
(.branch 3654 64333
(.branch 3618 64261
(.branch 3600 64119
(.branch 3591 64117
(.branch 3587 64141
(.branch 3585 64213
(.branch 3584 64429
(.branch 3583 64188
.empty
.empty)
.empty)
(.branch 3586 64309
.empty
.empty))
(.branch 3589 64237
(.branch 3588 64405
.empty
.empty)
(.branch 3590 64333
.empty
.empty)))
(.branch 3596 64166
(.branch 3594 64262
(.branch 3593 64358
(.branch 3592 64190
.empty
.empty)
.empty)
(.branch 3595 64478
.empty
.empty))
(.branch 3598 64286
(.branch 3597 64382
.empty
.empty)
(.branch 3599 64454
.empty
.empty))))
(.branch 3609 64332
(.branch 3605 64311
(.branch 3603 64407
(.branch 3602 64239
(.branch 3601 64335
.empty
.empty)
.empty)
(.branch 3604 64143
.empty
.empty))
(.branch 3607 64431
(.branch 3606 64215
.empty
.empty)
(.branch 3608 64116
.empty
.empty)))
(.branch 3614 64212
(.branch 3612 64140
(.branch 3611 64404
(.branch 3610 64236
.empty
.empty)
.empty)
(.branch 3613 64308
.empty
.empty))
(.branch 3616 64189
(.branch 3615 64428
.empty
.empty)
(.branch 3617 64357
.empty
.empty)))))
(.branch 3636 64479
(.branch 3627 64142
(.branch 3623 64453
(.branch 3621 64381
(.branch 3620 64165
(.branch 3619 64477
.empty
.empty)
.empty)
(.branch 3622 64285
.empty
.empty))
(.branch 3625 64214
(.branch 3624 64430
.empty
.empty)
(.branch 3626 64310
.empty
.empty)))
(.branch 3632 64455
(.branch 3630 64334
(.branch 3629 64238
(.branch 3628 64406
.empty
.empty)
.empty)
(.branch 3631 64118
.empty
.empty))
(.branch 3634 64383
(.branch 3633 64287
.empty
.empty)
(.branch 3635 64167
.empty
.empty))))
(.branch 3645 64260
(.branch 3641 64284
(.branch 3639 64191
(.branch 3638 64359
(.branch 3637 64263
.empty
.empty)
.empty)
(.branch 3640 64452
.empty
.empty))
(.branch 3643 64164
(.branch 3642 64380
.empty
.empty)
(.branch 3644 64476
.empty
.empty)))
(.branch 3650 64309
(.branch 3648 64429
(.branch 3647 64188
(.branch 3646 64356
.empty
.empty)
.empty)
(.branch 3649 64213
.empty
.empty))
(.branch 3652 64405
(.branch 3651 64141
.empty
.empty)
(.branch 3653 64237
.empty
.empty))))))
(.branch 3690 58647
(.branch 3672 64116
(.branch 3663 64454
(.branch 3659 64478
(.branch 3657 64358
(.branch 3656 64190
(.branch 3655 64117
.empty
.empty)
.empty)
(.branch 3658 64262
.empty
.empty))
(.branch 3661 64382
(.branch 3660 64166
.empty
.empty)
(.branch 3662 64286
.empty
.empty)))
(.branch 3668 64143
(.branch 3666 64239
(.branch 3665 64335
(.branch 3664 64119
.empty
.empty)
.empty)
(.branch 3667 64407
.empty
.empty))
(.branch 3670 64215
(.branch 3669 64311
.empty
.empty)
(.branch 3671 64431
.empty
.empty))))
(.branch 3681 64357
(.branch 3677 64308
(.branch 3675 64404
(.branch 3674 64236
(.branch 3673 64332
.empty
.empty)
.empty)
(.branch 3676 64140
.empty
.empty))
(.branch 3679 64428
(.branch 3678 64212
.empty
.empty)
(.branch 3680 64189
.empty
.empty)))
(.branch 3686 64285
(.branch 3684 64165
(.branch 3683 64477
(.branch 3682 64261
.empty
.empty)
.empty)
(.branch 3685 64381
.empty
.empty))
(.branch 3688 58645
(.branch 3687 64453
.empty
.empty)
(.branch 3689 58716
.empty
.empty)))))
(.branch 3708 58503
(.branch 3699 58575
(.branch 3695 58479
(.branch 3693 58477
(.branch 3692 58500
(.branch 3691 58718
.empty
.empty)
.empty)
(.branch 3694 58502
.empty
.empty))
(.branch 3697 58573
(.branch 3696 58596
.empty
.empty)
(.branch 3698 58598
.empty
.empty)))
(.branch 3704 58646
(.branch 3702 58359
(.branch 3701 58428
(.branch 3700 58357
.empty
.empty)
.empty)
(.branch 3703 58430
.empty
.empty))
(.branch 3706 58644
(.branch 3705 58719
.empty
.empty)
(.branch 3707 58717
.empty
.empty))))
(.branch 3717 58431
(.branch 3713 58574
(.branch 3711 58476
(.branch 3710 58501
(.branch 3709 58478
.empty
.empty)
.empty)
(.branch 3712 58599
.empty
.empty))
(.branch 3715 58572
(.branch 3714 58597
.empty
.empty)
(.branch 3716 58358
.empty
.empty)))
(.branch 3721 58405
(.branch 3719 58429
(.branch 3718 58356
.empty
.empty)
(.branch 3720 58380
.empty
.empty))
(.branch 3723 58407
(.branch 3722 58382
.empty
.empty)
(.branch 3724 58621
.empty
.empty))))))))
(.branch 3868 68549
(.branch 3797 58693
(.branch 3761 58573
(.branch 3743 58549
(.branch 3734 58670
(.branch 3730 58527
(.branch 3728 58525
(.branch 3727 58550
(.branch 3726 58623
.empty
.empty)
.empty)
(.branch 3729 58452
.empty
.empty))
(.branch 3732 58668
(.branch 3731 58454
.empty
.empty)
(.branch 3733 58693
.empty
.empty)))
(.branch 3739 58404
(.branch 3737 58406
(.branch 3736 58383
(.branch 3735 58695
.empty
.empty)
.empty)
(.branch 3738 58381
.empty
.empty))
(.branch 3741 58551
(.branch 3740 58622
.empty
.empty)
(.branch 3742 58620
.empty
.empty))))
(.branch 3752 58645
(.branch 3748 58671
(.branch 3746 58524
(.branch 3745 58455
(.branch 3744 58526
.empty
.empty)
.empty)
(.branch 3747 58453
.empty
.empty))
(.branch 3750 58669
(.branch 3749 58694
.empty
.empty)
(.branch 3751 58692
.empty
.empty)))
(.branch 3757 58477
(.branch 3755 58718
(.branch 3754 58647
(.branch 3753 58716
.empty
.empty)
.empty)
(.branch 3756 58500
.empty
.empty))
(.branch 3759 58479
(.branch 3758 58502
.empty
.empty)
(.branch 3760 58596
.empty
.empty)))))
(.branch 3779 58572
(.branch 3770 58644
(.branch 3766 58359
(.branch 3764 58357
(.branch 3763 58575
(.branch 3762 58598
.empty
.empty)
.empty)
(.branch 3765 58428
.empty
.empty))
(.branch 3768 58646
(.branch 3767 58430
.empty
.empty)
(.branch 3769 58719
.empty
.empty)))
(.branch 3775 58476
(.branch 3773 58478
(.branch 3772 58503
(.branch 3771 58717
.empty
.empty)
.empty)
(.branch 3774 58501
.empty
.empty))
(.branch 3777 58574
(.branch 3776 58599
.empty
.empty)
(.branch 3778 58597
.empty
.empty))))
(.branch 3788 58621
(.branch 3784 58380
(.branch 3782 58356
(.branch 3781 58431
(.branch 3780 58358
.empty
.empty)
.empty)
(.branch 3783 58429
.empty
.empty))
(.branch 3786 58382
(.branch 3785 58405
.empty
.empty)
(.branch 3787 58407
.empty
.empty)))
(.branch 3793 58452
(.branch 3791 58550
(.branch 3790 58623
(.branch 3789 58548
.empty
.empty)
.empty)
(.branch 3792 58525
.empty
.empty))
(.branch 3795 58454
(.branch 3794 58527
.empty
.empty)
(.branch 3796 58668
.empty
.empty))))))
(.branch 3833 68695
(.branch 3815 58692
(.branch 3806 58620
(.branch 3802 58381
(.branch 3800 58383
(.branch 3799 58695
(.branch 3798 58670
.empty
.empty)
.empty)
(.branch 3801 58406
.empty
.empty))
(.branch 3804 58622
(.branch 3803 58404
.empty
.empty)
(.branch 3805 58551
.empty
.empty)))
(.branch 3811 58453
(.branch 3809 58455
(.branch 3808 58526
(.branch 3807 58549
.empty
.empty)
.empty)
(.branch 3810 58524
.empty
.empty))
(.branch 3813 58694
(.branch 3812 58671
.empty
.empty)
(.branch 3814 58669
.empty
.empty))))
(.branch 3824 68527
(.branch 3820 68431
(.branch 3818 68404
(.branch 3817 68623
(.branch 3816 68647
.empty
.empty)
.empty)
(.branch 3819 68380
.empty
.empty))
(.branch 3822 68572
(.branch 3821 68455
.empty
.empty)
(.branch 3823 68596
.empty
.empty)))
(.branch 3829 68335
(.branch 3827 68500
(.branch 3826 68476
(.branch 3825 68551
.empty
.empty)
.empty)
(.branch 3828 68359
.empty
.empty))
(.branch 3831 68668
(.branch 3830 68692
.empty
.empty)
(.branch 3832 68671
.empty
.empty)))))
(.branch 3851 68622
(.branch 3842 68452
(.branch 3838 68548
(.branch 3836 68503
(.branch 3835 68356
(.branch 3834 68332
.empty
.empty)
.empty)
(.branch 3837 68479
.empty
.empty))
(.branch 3840 68599
(.branch 3839 68524
.empty
.empty)
(.branch 3841 68575
.empty
.empty)))
(.branch 3847 68644
(.branch 3845 68407
(.branch 3844 68383
(.branch 3843 68428
.empty
.empty)
.empty)
(.branch 3846 68620
.empty
.empty))
(.branch 3849 68381
(.branch 3848 68405
.empty
.empty)
(.branch 3850 68646
.empty
.empty))))
(.branch 3860 68693
(.branch 3856 68477
(.branch 3854 68430
(.branch 3853 68597
(.branch 3852 68573
.empty
.empty)
.empty)
(.branch 3855 68454
.empty
.empty))
(.branch 3858 68526
(.branch 3857 68501
.empty
.empty)
(.branch 3859 68550
.empty
.empty)))
(.branch 3864 68333
(.branch 3862 68358
(.branch 3861 68669
.empty
.empty)
(.branch 3863 68334
.empty
.empty))
(.branch 3866 68670
(.branch 3865 68357
.empty
.empty)
(.branch 3867 68694
.empty
.empty)))))))
(.branch 3940 68621
(.branch 3904 68599
(.branch 3886 68572
(.branch 3877 68645
(.branch 3873 68429
(.branch 3871 68478
(.branch 3870 68502
(.branch 3869 68525
.empty
.empty)
.empty)
(.branch 3872 68453
.empty
.empty))
(.branch 3875 68574
(.branch 3874 68598
.empty
.empty)
(.branch 3876 68621
.empty
.empty)))
(.branch 3882 68404
(.branch 3880 68647
(.branch 3879 68406
(.branch 3878 68382
.empty
.empty)
.empty)
(.branch 3881 68623
.empty
.empty))
(.branch 3884 68431
(.branch 3883 68380
.empty
.empty)
(.branch 3885 68455
.empty
.empty))))
(.branch 3895 68668
(.branch 3891 68500
(.branch 3889 68551
(.branch 3888 68527
(.branch 3887 68596
.empty
.empty)
.empty)
(.branch 3890 68476
.empty
.empty))
(.branch 3893 68335
(.branch 3892 68359
.empty
.empty)
(.branch 3894 68692
.empty
.empty)))
(.branch 3900 68503
(.branch 3898 68332
(.branch 3897 68695
(.branch 3896 68671
.empty
.empty)
.empty)
(.branch 3899 68356
.empty
.empty))
(.branch 3902 68548
(.branch 3901 68479
.empty
.empty)
(.branch 3903 68524
.empty
.empty)))))
(.branch 3922 68526
(.branch 3913 68381
(.branch 3909 68407
(.branch 3907 68428
(.branch 3906 68452
(.branch 3905 68575
.empty
.empty)
.empty)
(.branch 3908 68383
.empty
.empty))
(.branch 3911 68644
(.branch 3910 68620
.empty
.empty)
(.branch 3912 68405
.empty
.empty)))
(.branch 3918 68430
(.branch 3916 68573
(.branch 3915 68622
(.branch 3914 68646
.empty
.empty)
.empty)
(.branch 3917 68597
.empty
.empty))
(.branch 3920 68477
(.branch 3919 68454
.empty
.empty)
(.branch 3921 68501
.empty
.empty))))
(.branch 3931 68694
(.branch 3927 68334
(.branch 3925 68669
(.branch 3924 68693
(.branch 3923 68550
.empty
.empty)
.empty)
(.branch 3926 68358
.empty
.empty))
(.branch 3929 68357
(.branch 3928 68333
.empty
.empty)
(.branch 3930 68670
.empty
.empty)))
(.branch 3936 68453
(.branch 3934 68502
(.branch 3933 68525
(.branch 3932 68549
.empty
.empty)
.empty)
(.branch 3935 68478
.empty
.empty))
(.branch 3938 68598
(.branch 3937 68429
.empty
.empty)
(.branch 3939 68574
.empty
.empty))))))
(.branch 3976 54125
(.branch 3958 54246
(.branch 3949 54340
(.branch 3945 54295
(.branch 3943 68406
(.branch 3942 68382
(.branch 3941 68645
.empty
.empty)
.empty)
(.branch 3944 54124
.empty
.empty))
(.branch 3947 54412
(.branch 3946 54391
.empty
.empty)
(.branch 3948 54463
.empty
.empty)))
(.branch 3954 54389
(.branch 3952 54126
(.branch 3951 54175
(.branch 3950 54244
.empty
.empty)
.empty)
(.branch 3953 54293
.empty
.empty))
(.branch 3956 54461
(.branch 3955 54414
.empty
.empty)
(.branch 3957 54342
.empty
.empty))))
(.branch 3967 54484
(.branch 3963 54151
(.branch 3961 54364
(.branch 3960 54439
(.branch 3959 54173
.empty
.empty)
.empty)
(.branch 3962 54268
.empty
.empty))
(.branch 3965 54223
(.branch 3964 54196
.empty
.empty)
(.branch 3966 54319
.empty
.empty)))
(.branch 3972 54198
(.branch 3970 54270
(.branch 3969 54366
(.branch 3968 54437
.empty
.empty)
.empty)
(.branch 3971 54149
.empty
.empty))
(.branch 3974 54317
(.branch 3973 54221
.empty
.empty)
(.branch 3975 54486
.empty
.empty)))))
(.branch 3994 54269
(.branch 3985 54292
(.branch 3981 54341
(.branch 3979 54413
(.branch 3978 54390
(.branch 3977 54294
.empty
.empty)
.empty)
(.branch 3980 54462
.empty
.empty))
(.branch 3983 54174
(.branch 3982 54245
.empty
.empty)
(.branch 3984 54127
.empty
.empty)))
(.branch 3990 54247
(.branch 3988 54460
(.branch 3987 54415
(.branch 3986 54388
.empty
.empty)
.empty)
(.branch 3989 54343
.empty
.empty))
(.branch 3992 54438
(.branch 3991 54172
.empty
.empty)
(.branch 3993 54365
.empty
.empty))))
(.branch 4003 54148
(.branch 3999 54485
(.branch 3997 54222
(.branch 3996 54197
(.branch 3995 54150
.empty
.empty)
.empty)
(.branch 3998 54318
.empty
.empty))
(.branch 4001 54367
(.branch 4000 54436
.empty
.empty)
(.branch 4002 54271
.empty
.empty)))
(.branch 4007 54487
(.branch 4005 54220
(.branch 4004 54199
.empty
.empty)
(.branch 4006 54316
.empty
.empty))
(.branch 4009 54295
(.branch 4008 54124
.empty
.empty)
(.branch 4010 54391
.empty
.empty)))))))))
(.branch 4298 68678
(.branch 4155 54471
(.branch 4083 54399
(.branch 4047 54174
(.branch 4029 54223
(.branch 4020 54461
(.branch 4016 54126
(.branch 4014 54244
(.branch 4013 54340
(.branch 4012 54463
.empty
.empty)
.empty)
(.branch 4015 54175
.empty
.empty))
(.branch 4018 54389
(.branch 4017 54293
.empty
.empty)
(.branch 4019 54414
.empty
.empty)))
(.branch 4025 54364
(.branch 4023 54173
(.branch 4022 54246
(.branch 4021 54342
.empty
.empty)
.empty)
(.branch 4024 54439
.empty
.empty))
(.branch 4027 54151
(.branch 4026 54268
.empty
.empty)
(.branch 4028 54196
.empty
.empty))))
(.branch 4038 54317
(.branch 4034 54270
(.branch 4032 54437
(.branch 4031 54484
(.branch 4030 54319
.empty
.empty)
.empty)
(.branch 4033 54366
.empty
.empty))
(.branch 4036 54198
(.branch 4035 54149
.empty
.empty)
(.branch 4037 54221
.empty
.empty)))
(.branch 4043 54413
(.branch 4041 54294
(.branch 4040 54125
(.branch 4039 54486
.empty
.empty)
.empty)
(.branch 4042 54390
.empty
.empty))
(.branch 4045 54341
(.branch 4044 54462
.empty
.empty)
(.branch 4046 54245
.empty
.empty)))))
(.branch 4065 54367
(.branch 4056 54438
(.branch 4052 54460
(.branch 4050 54388
(.branch 4049 54292
(.branch 4048 54127
.empty
.empty)
.empty)
(.branch 4051 54415
.empty
.empty))
(.branch 4054 54247
(.branch 4053 54343
.empty
.empty)
(.branch 4055 54172
.empty
.empty)))
(.branch 4061 54222
(.branch 4059 54150
(.branch 4058 54269
(.branch 4057 54365
.empty
.empty)
.empty)
(.branch 4060 54197
.empty
.empty))
(.branch 4063 54485
(.branch 4062 54318
.empty
.empty)
(.branch 4064 54436
.empty
.empty))))
(.branch 4074 54135
(.branch 4070 54316
(.branch 4068 54199
(.branch 4067 54148
(.branch 4066 54271
.empty
.empty)
.empty)
(.branch 4069 54220
.empty
.empty))
(.branch 4072 54132
(.branch 4071 54487
.empty
.empty)
(.branch 4073 54445
.empty
.empty)))
(.branch 4079 54303
(.branch 4077 54300
(.branch 4076 54373
(.branch 4075 54446
.empty
.empty)
.empty)
(.branch 4078 54374
.empty
.empty))
(.branch 4081 54396
(.branch 4080 54277
.empty
.empty)
(.branch 4082 54278
.empty
.empty))))))
(.branch 4119 54156
(.branch 4101 54180
(.branch 4092 54348
(.branch 4088 54205
(.branch 4086 54423
(.branch 4085 54157
(.branch 4084 54420
.empty
.empty)
.empty)
(.branch 4087 54158
.empty
.empty))
(.branch 4090 54206
(.branch 4089 54468
.empty
.empty)
(.branch 4091 54471
.empty
.empty)))
(.branch 4097 54325
(.branch 4095 54230
(.branch 4094 54351
(.branch 4093 54229
.empty
.empty)
.empty)
(.branch 4096 54252
.empty
.empty))
(.branch 4099 54326
(.branch 4098 54255
.empty
.empty)
(.branch 4100 54493
.empty
.empty))))
(.branch 4110 54372
(.branch 4106 54133
(.branch 4104 54134
(.branch 4103 54183
(.branch 4102 54494
.empty
.empty)
.empty)
(.branch 4105 54447
.empty
.empty))
(.branch 4108 54375
(.branch 4107 54444
.empty
.empty)
(.branch 4109 54302
.empty
.empty)))
(.branch 4115 54397
(.branch 4113 54398
(.branch 4112 54279
(.branch 4111 54301
.empty
.empty)
.empty)
(.branch 4114 54276
.empty
.empty))
(.branch 4117 54159
(.branch 4116 54422
.empty
.empty)
(.branch 4118 54421
.empty
.empty)))))
(.branch 4137 54445
(.branch 4128 54254
(.branch 4124 54350
(.branch 4122 54204
(.branch 4121 54470
(.branch 4120 54207
.empty
.empty)
.empty)
(.branch 4123 54469
.empty
.empty))
(.branch 4126 54349
(.branch 4125 54231
.empty
.empty)
(.branch 4127 54228
.empty
.empty)))
(.branch 4133 54182
(.branch 4131 54324
(.branch 4130 54253
(.branch 4129 54327
.empty
.empty)
.empty)
(.branch 4132 54495
.empty
.empty))
(.branch 4135 54181
(.branch 4134 54492
.empty
.empty)
(.branch 4136 54132
.empty
.empty))))
(.branch 4146 54278
(.branch 4142 54374
(.branch 4140 54373
(.branch 4139 54446
(.branch 4138 54135
.empty
.empty)
.empty)
(.branch 4141 54300
.empty
.empty))
(.branch 4144 54277
(.branch 4143 54303
.empty
.empty)
(.branch 4145 54396
.empty
.empty)))
(.branch 4151 54158
(.branch 4149 54157
(.branch 4148 54420
(.branch 4147 54399
.empty
.empty)
.empty)
(.branch 4150 54423
.empty
.empty))
(.branch 4153 54468
(.branch 4152 54205
.empty
.empty)
(.branch 4154 54206
.empty
.empty)))))))
(.branch 4227 68557
(.branch 4191 54228
(.branch 4173 54302
(.branch 4164 54493
(.branch 4160 54252
(.branch 4158 54351
(.branch 4157 54229
(.branch 4156 54348
.empty
.empty)
.empty)
(.branch 4159 54230
.empty
.empty))
(.branch 4162 54255
(.branch 4161 54325
.empty
.empty)
(.branch 4163 54326
.empty
.empty)))
(.branch 4169 54447
(.branch 4167 54183
(.branch 4166 54494
(.branch 4165 54180
.empty
.empty)
.empty)
(.branch 4168 54134
.empty
.empty))
(.branch 4171 54444
(.branch 4170 54133
.empty
.empty)
(.branch 4172 54375
.empty
.empty))))
(.branch 4182 54421
(.branch 4178 54276
(.branch 4176 54279
(.branch 4175 54301
(.branch 4174 54372
.empty
.empty)
.empty)
(.branch 4177 54398
.empty
.empty))
(.branch 4180 54422
(.branch 4179 54397
.empty
.empty)
(.branch 4181 54159
.empty
.empty)))
(.branch 4187 54469
(.branch 4185 54470
(.branch 4184 54207
(.branch 4183 54156
.empty
.empty)
.empty)
(.branch 4186 54204
.empty
.empty))
(.branch 4189 54231
(.branch 4188 54350
.empty
.empty)
(.branch 4190 54349
.empty
.empty)))))
(.branch 4209 68559
(.branch 4200 68655
(.branch 4196 54495
(.branch 4194 54253
(.branch 4193 54327
(.branch 4192 54254
.empty
.empty)
.empty)
(.branch 4195 54324
.empty
.empty))
(.branch 4198 54492
(.branch 4197 54182
.empty
.empty)
(.branch 4199 54181
.empty
.empty)))
(.branch 4205 68463
(.branch 4203 68702
(.branch 4202 68342
(.branch 4201 68391
.empty
.empty)
.empty)
(.branch 4204 68583
.empty
.empty))
(.branch 4207 68534
(.branch 4206 68510
.empty
.empty)
(.branch 4208 68487
.empty
.empty))))
(.branch 4218 68653
(.branch 4214 68630
(.branch 4212 68367
(.branch 4211 68438
(.branch 4210 68606
.empty
.empty)
.empty)
(.branch 4213 68679
.empty
.empty))
(.branch 4216 68340
(.branch 4215 68414
.empty
.empty)
(.branch 4217 68700
.empty
.empty)))
(.branch 4223 68461
(.branch 4221 68532
(.branch 4220 68508
(.branch 4219 68389
.empty
.empty)
.empty)
(.branch 4222 68581
.empty
.empty))
(.branch 4225 68436
(.branch 4224 68604
.empty
.empty)
(.branch 4226 68485
.empty
.empty))))))
(.branch 4263 68341
(.branch 4245 68343
(.branch 4236 68439
(.branch 4232 68415
(.branch 4230 68365
(.branch 4229 68412
(.branch 4228 68628
.empty
.empty)
.empty)
(.branch 4231 68677
.empty
.empty))
(.branch 4234 68678
(.branch 4233 68631
.empty
.empty)
(.branch 4235 68366
.empty
.empty)))
(.branch 4241 68511
(.branch 4239 68486
(.branch 4238 68558
(.branch 4237 68607
.empty
.empty)
.empty)
(.branch 4240 68535
.empty
.empty))
(.branch 4243 68582
(.branch 4242 68462
.empty
.empty)
(.branch 4244 68703
.empty
.empty))))
(.branch 4254 68437
(.branch 4250 68413
(.branch 4248 68676
(.branch 4247 68654
(.branch 4246 68390
.empty
.empty)
.empty)
(.branch 4249 68364
.empty
.empty))
(.branch 4252 68556
(.branch 4251 68629
.empty
.empty)
(.branch 4253 68484
.empty
.empty)))
(.branch 4259 68509
(.branch 4257 68580
(.branch 4256 68460
(.branch 4255 68605
.empty
.empty)
.empty)
(.branch 4258 68533
.empty
.empty))
(.branch 4261 68652
(.branch 4260 68388
.empty
.empty)
(.branch 4262 68701
.empty
.empty)))))
(.branch 4281 68700
(.branch 4272 68487
(.branch 4268 68583
(.branch 4266 68342
(.branch 4265 68391
(.branch 4264 68655
.empty
.empty)
.empty)
(.branch 4267 68702
.empty
.empty))
(.branch 4270 68510
(.branch 4269 68463
.empty
.empty)
(.branch 4271 68534
.empty
.empty)))
(.branch 4277 68679
(.branch 4275 68438
(.branch 4274 68606
(.branch 4273 68559
.empty
.empty)
.empty)
(.branch 4276 68367
.empty
.empty))
(.branch 4279 68414
(.branch 4278 68630
.empty
.empty)
(.branch 4280 68340
.empty
.empty))))
(.branch 4290 68485
(.branch 4286 68581
(.branch 4284 68508
(.branch 4283 68389
(.branch 4282 68653
.empty
.empty)
.empty)
(.branch 4285 68532
.empty
.empty))
(.branch 4288 68604
(.branch 4287 68461
.empty
.empty)
(.branch 4289 68436
.empty
.empty)))
(.branch 4294 68365
(.branch 4292 68628
(.branch 4291 68557
.empty
.empty)
(.branch 4293 68412
.empty
.empty))
(.branch 4296 68415
(.branch 4295 68677
.empty
.empty)
(.branch 4297 68631
.empty
.empty))))))))
(.branch 4441 58660
(.branch 4370 58517
(.branch 4334 58612
(.branch 4316 68556
(.branch 4307 68582
(.branch 4303 68486
(.branch 4301 68607
(.branch 4300 68439
(.branch 4299 68366
.empty
.empty)
.empty)
(.branch 4302 68558
.empty
.empty))
(.branch 4305 68511
(.branch 4304 68535
.empty
.empty)
(.branch 4306 68462
.empty
.empty)))
(.branch 4312 68676
(.branch 4310 68390
(.branch 4309 68343
(.branch 4308 68703
.empty
.empty)
.empty)
(.branch 4311 68654
.empty
.empty))
(.branch 4314 68413
(.branch 4313 68364
.empty
.empty)
(.branch 4315 68629
.empty
.empty))))
(.branch 4325 68652
(.branch 4321 68580
(.branch 4319 68605
(.branch 4318 68437
(.branch 4317 68484
.empty
.empty)
.empty)
(.branch 4320 68460
.empty
.empty))
(.branch 4323 68509
(.branch 4322 68533
.empty
.empty)
(.branch 4324 68388
.empty
.empty)))
(.branch 4330 58638
(.branch 4328 58637
(.branch 4327 68341
(.branch 4326 68701
.empty
.empty)
.empty)
(.branch 4329 58399
.empty
.empty))
(.branch 4332 58615
(.branch 4331 58396
.empty
.empty)
(.branch 4333 58469
.empty
.empty)))))
(.branch 4352 58541
(.branch 4343 58684
(.branch 4339 58566
(.branch 4337 58565
(.branch 4336 58519
(.branch 4335 58470
.empty
.empty)
.empty)
(.branch 4338 58516
.empty
.empty))
(.branch 4341 58687
(.branch 4340 58349
.empty
.empty)
(.branch 4342 58350
.empty
.empty)))
(.branch 4348 58445
(.branch 4346 58420
(.branch 4345 58661
(.branch 4344 58423
.empty
.empty)
.empty)
(.branch 4347 58662
.empty
.empty))
(.branch 4350 58446
(.branch 4349 58591
.empty
.empty)
(.branch 4351 58588
.empty
.empty))))
(.branch 4361 58398
(.branch 4357 58373
(.branch 4355 58492
(.branch 4354 58542
(.branch 4353 58495
.empty
.empty)
.empty)
(.branch 4356 58711
.empty
.empty))
(.branch 4359 58374
(.branch 4358 58708
.empty
.empty)
(.branch 4360 58636
.empty
.empty)))
(.branch 4366 58613
(.branch 4364 58614
(.branch 4363 58397
(.branch 4362 58639
.empty
.empty)
.empty)
(.branch 4365 58468
.empty
.empty))
(.branch 4368 58518
(.branch 4367 58471
.empty
.empty)
(.branch 4369 58564
.empty
.empty))))))
(.branch 4406 58350
(.branch 4388 58710
(.branch 4379 58663
(.branch 4375 58685
(.branch 4373 58686
(.branch 4372 58348
(.branch 4371 58567
.empty
.empty)
.empty)
(.branch 4374 58351
.empty
.empty))
(.branch 4377 58660
(.branch 4376 58422
.empty
.empty)
(.branch 4378 58421
.empty
.empty)))
(.branch 4384 58540
(.branch 4382 58447
(.branch 4381 58590
(.branch 4380 58444
.empty
.empty)
.empty)
(.branch 4383 58589
.empty
.empty))
(.branch 4386 58543
(.branch 4385 58494
.empty
.empty)
(.branch 4387 58493
.empty
.empty))))
(.branch 4397 58469
(.branch 4393 58399
(.branch 4391 58375
(.branch 4390 58709
(.branch 4389 58372
.empty
.empty)
.empty)
(.branch 4392 58637
.empty
.empty))
(.branch 4395 58396
(.branch 4394 58638
.empty
.empty)
(.branch 4396 58615
.empty
.empty)))
(.branch 4402 58516
(.branch 4400 58519
(.branch 4399 58470
(.branch 4398 58612
.empty
.empty)
.empty)
(.branch 4401 58565
.empty
.empty))
(.branch 4404 58349
(.branch 4403 58566
.empty
.empty)
(.branch 4405 58687
.empty
.empty)))))
(.branch 4424 58636
(.branch 4415 58588
(.branch 4411 58662
(.branch 4409 58661
(.branch 4408 58423
(.branch 4407 58684
.empty
.empty)
.empty)
(.branch 4410 58420
.empty
.empty))
(.branch 4413 58591
(.branch 4412 58445
.empty
.empty)
(.branch 4414 58446
.empty
.empty)))
(.branch 4420 58711
(.branch 4418 58542
(.branch 4417 58495
(.branch 4416 58541
.empty
.empty)
.empty)
(.branch 4419 58492
.empty
.empty))
(.branch 4422 58708
(.branch 4421 58373
.empty
.empty)
(.branch 4423 58374
.empty
.empty))))
(.branch 4433 58564
(.branch 4429 58468
(.branch 4427 58397
(.branch 4426 58639
(.branch 4425 58398
.empty
.empty)
.empty)
(.branch 4428 58614
.empty
.empty))
(.branch 4431 58471
(.branch 4430 58613
.empty
.empty)
(.branch 4432 58518
.empty
.empty)))
(.branch 4437 58686
(.branch 4435 58567
(.branch 4434 58517
.empty
.empty)
(.branch 4436 58348
.empty
.empty))
(.branch 4439 58685
(.branch 4438 58351
.empty
.empty)
(.branch 4440 58422
.empty
.empty)))))))
(.branch 4513 64327
(.branch 4477 64229
(.branch 4459 64108
(.branch 4450 58543
(.branch 4446 58447
(.branch 4444 58444
(.branch 4443 58663
(.branch 4442 58421
.empty
.empty)
.empty)
(.branch 4445 58590
.empty
.empty))
(.branch 4448 58540
(.branch 4447 58589
.empty
.empty)
(.branch 4449 58494
.empty
.empty)))
(.branch 4455 58375
(.branch 4453 58372
(.branch 4452 58710
(.branch 4451 58493
.empty
.empty)
.empty)
(.branch 4454 58709
.empty
.empty))
(.branch 4457 64421
(.branch 4456 64422
.empty
.empty)
(.branch 4458 64111
.empty
.empty))))
(.branch 4468 64134
(.branch 4464 64255
(.branch 4462 64278
(.branch 4461 64348
(.branch 4460 64351
.empty
.empty)
.empty)
(.branch 4463 64277
.empty
.empty))
(.branch 4466 64374
(.branch 4465 64252
.empty
.empty)
(.branch 4467 64373
.empty
.empty)))
(.branch 4473 64156
(.branch 4471 64396
(.branch 4470 64399
(.branch 4469 64133
.empty
.empty)
.empty)
(.branch 4472 64159
.empty
.empty))
(.branch 4475 64469
(.branch 4474 64470
.empty
.empty)
(.branch 4476 64230
.empty
.empty)))))
(.branch 4495 64279
(.branch 4486 64182
(.branch 4482 64207
(.branch 4480 64326
(.branch 4479 64300
(.branch 4478 64303
.empty
.empty)
.empty)
(.branch 4481 64325
.empty
.empty))
(.branch 4484 64447
(.branch 4483 64204
.empty
.empty)
(.branch 4485 64444
.empty
.empty)))
(.branch 4491 64110
(.branch 4489 64423
(.branch 4488 64420
(.branch 4487 64181
.empty
.empty)
.empty)
(.branch 4490 64109
.empty
.empty))
(.branch 4493 64350
(.branch 4492 64349
.empty
.empty)
(.branch 4494 64276
.empty
.empty))))
(.branch 4504 64157
(.branch 4500 64132
(.branch 4498 64372
(.branch 4497 64254
(.branch 4496 64253
.empty
.empty)
.empty)
(.branch 4499 64375
.empty
.empty))
(.branch 4502 64397
(.branch 4501 64135
.empty
.empty)
(.branch 4503 64398
.empty
.empty)))
(.branch 4509 64231
(.branch 4507 64471
(.branch 4506 64468
(.branch 4505 64158
.empty
.empty)
.empty)
(.branch 4508 64228
.empty
.empty))
(.branch 4511 64302
(.branch 4510 64301
.empty
.empty)
(.branch 4512 64324
.empty
.empty))))))
(.branch 4549 64444
(.branch 4531 64373
(.branch 4522 64111
(.branch 4518 64180
(.branch 4516 64445
(.branch 4515 64206
(.branch 4514 64205
.empty
.empty)
.empty)
(.branch 4517 64446
.empty
.empty))
(.branch 4520 64422
(.branch 4519 64183
.empty
.empty)
(.branch 4521 64421
.empty
.empty)))
(.branch 4527 64277
(.branch 4525 64348
(.branch 4524 64351
(.branch 4523 64108
.empty
.empty)
.empty)
(.branch 4526 64278
.empty
.empty))
(.branch 4529 64252
(.branch 4528 64255
.empty
.empty)
(.branch 4530 64374
.empty
.empty))))
(.branch 4540 64230
(.branch 4536 64159
(.branch 4534 64399
(.branch 4533 64133
(.branch 4532 64134
.empty
.empty)
.empty)
(.branch 4535 64396
.empty
.empty))
(.branch 4538 64470
(.branch 4537 64156
.empty
.empty)
(.branch 4539 64469
.empty
.empty)))
(.branch 4545 64325
(.branch 4543 64300
(.branch 4542 64303
(.branch 4541 64229
.empty
.empty)
.empty)
(.branch 4544 64326
.empty
.empty))
(.branch 4547 64204
(.branch 4546 64207
.empty
.empty)
(.branch 4548 64447
.empty
.empty)))))
(.branch 4567 64398
(.branch 4558 64276
(.branch 4554 64109
(.branch 4552 64420
(.branch 4551 64181
(.branch 4550 64182
.empty
.empty)
.empty)
(.branch 4553 64423
.empty
.empty))
(.branch 4556 64349
(.branch 4555 64110
.empty
.empty)
(.branch 4557 64350
.empty
.empty)))
(.branch 4563 64375
(.branch 4561 64254
(.branch 4560 64253
(.branch 4559 64279
.empty
.empty)
.empty)
(.branch 4562 64372
.empty
.empty))
(.branch 4565 64135
(.branch 4564 64132
.empty
.empty)
(.branch 4566 64397
.empty
.empty))))
(.branch 4576 64324
(.branch 4572 64228
(.branch 4570 64468
(.branch 4569 64158
(.branch 4568 64157
.empty
.empty)
.empty)
(.branch 4571 64471
.empty
.empty))
(.branch 4574 64301
(.branch 4573 64231
.empty
.empty)
(.branch 4575 64302
.empty
.empty)))
(.branch 4580 64445
(.branch 4578 64205
(.branch 4577 64327
.empty
.empty)
(.branch 4579 64206
.empty
.empty))
(.branch 4582 64180
(.branch 4581 64446
.empty
.empty)
(.branch 4583 64183
.empty
.empty))))))))))))

/-- Candidate original inverse preferred labels; all complete images are checked separately. -/
def generatedAxisGlobalOddFourthSelectedSourceIndex (k : Fin 4) (j : Fin 4584) : Fin 98280 :=
  (generatedAxisGlobalSparseLookup (![generatedAxisGlobalOddFourthSelectedSourceTree00, generatedAxisGlobalOddFourthSelectedSourceTree01, generatedAxisGlobalOddFourthSelectedSourceTree02, generatedAxisGlobalOddFourthSelectedSourceTree03] k) j.val).getD 0

/-- Candidate central bits, packed only to keep bounded kernel checks small. -/
def generatedAxisGlobalOddFourthSelectedPhaseBlocks : Fin 4 → Fin 72 → ℕ :=
![
  ![11126886711658555175, 9100477514049499370, 11955610920643625537, 417047531930622733, 5201383526850513785, 4706953869381969578, 14744464020142023862, 7517830326032948909, 7797592310984760474, 3746978162748592953, 4340558614361850819, 14743039220223307836, 7189445510819099545, 14742927695034254672, 17568444028857980467, 3850355146056751461, 1127489178782610799, 1138549129265531919, 3732414334139157708, 16276521648204795084, 14106184558159142610, 3148775679597491004, 17361600963062886699, 3462146388501974220, 274441610207628480, 3913690958737243343, 18183681863281817248, 3334787317850423344, 3723012540411365149, 10055379448596122794, 11936226889388269026, 10079868502369042431, 14065586561372512884, 1302363894218686479, 6510781112318619117, 8929938837620789232, 3691826814660019437, 10661533178125877488, 43346679224595769, 12275222912307058022, 12275223401847215445, 17557676384404002133, 17557676315690389440, 14714329350657003456, 14714329584963957555, 14625036046649013043, 14625035646512288595, 3834193236030280531, 3834193627600767690, 4718972833495370442, 4718972248148902635, 2600967606401204971, 2600968135625965245, 4337905136930684605, 4337905055589180837, 11768814753936549285, 11768814892061869365, 14051512081999250741, 14051511859628321475, 922960393936415427, 922960017966957375, 6036420262357828415, 6036420840558079173, 14757227003077373125, 14757226376558555955, 4365842038005707571, 4365842183450853180, 4543075761266949948, 4543076440256790540, 13696782320864051212, 13696781811500373780, 537550575380],
  ![15141247374205797393, 9300205616313628746, 2551594375512099656, 15646264151225743277, 4917294881323003035, 8916044756567269896, 6416702068333482255, 2707151367999469201, 14076745738247574059, 3704607878185395516, 10863593576451184179, 7827531483014022038, 15498207296025681865, 12421199177943477106, 1717205905356267461, 3689516921079540606, 1085086912251940044, 6036289153718550528, 689173530260683356, 6244638949347660022, 16293216394181409898, 17944188402144069409, 5598778439612650384, 43066669991586011, 6179971127603848857, 1085366779039630275, 4340559644904718335, 6148914585715031235, 17115049308503845461, 13889287854564778312, 16939289714804310102, 3105159287483329394, 480918587444374401, 11484358628547561157, 15336021854022508451, 2006425289105724545, 6197914231124401026, 1095276294318347968, 13238070455720266767, 15572111685211066898, 15572111774516648834, 502555048916425602, 502555748356835951, 3863817770049456751, 3863817131280392284, 11501922099300753500, 11501922099310873334, 6172839928131734262, 6172840065683008170, 11936128174763911850, 11936128194896878245, 7350155355396659877, 7350155626175070105, 14746292169782394777, 14746291900259709900, 6510698020054709196, 6510698020062190245, 11936128196160084645, 11936128518282651045, 6944825115249321381, 6944824432248424185, 14581593493641037561, 14581593861308795475, 6050990016255216211, 6050990359856609594, 16436803472991516986, 16436802902967527233, 13191836226144773953, 13191836844776615284, 1446976782175694196, 1446976919643695182, 925792806990],
  ![6459308437775529088, 10714988395297610306, 11181544301335583078, 5446657024702916197, 15217095022877664685, 7868595205545027006, 14642444383225820363, 7256094108092353842, 1722768907693672089, 12876596076257142913, 1794527989537131812, 12876595183121143921, 3158357377710076452, 4809047441904839613, 15842341063628636715, 1722765553551203250, 8182504959812692094, 10272174798660931096, 16782803160150864359, 16652216751408158593, 9331150670124882062, 1794527766404103912, 9115593403584669553, 16710481627484553495, 9331995984115144817, 10264239570898419223, 16723978067472052711, 13672131423723460481, 1722769506942272212, 2655913116939774081, 3158222750050278322, 8174569697492980802, 1663941034626281752, 2655913116889388926, 3158222750050278322, 10272175100010550338, 16782803039083269863, 2655801168617400449, 15842340934211413069, 7393052571108301746, 7393052854151715225, 11067990150086039961, 11067990368273733990, 6531808912837351782, 6531808965433121370, 3689517531562400346, 3689517697150995660, 12297736068009282764, 12297735558912431445, 17298061554363290965, 17298061251119739120, 17361640510995886320, 17361640510981083120, 14068333805443158000, 14068334001739580220, 11936128067807527740, 11936128194896878245, 7393052801554340517, 7393053072342738585, 11067990368277063321, 11067990150089369190, 14106184869215823462, 14106185267081429820, 17361641284833166140, 17361640510981083120, 11053690625383665648, 11053691001366813030, 12297735631637223782, 12297735922553039445, 3732414997852432981, 3732414488745594060, 222469278924],
  ![17828819541330804119, 6136902938833520330, 12342868128247207338, 8233394235536741718, 1051125470465396879, 10039829310009734859, 15180889585172697770, 5113009072394384554, 10838359218671002670, 868122250750355817, 2170304286661820208, 17129180272788354168, 8410721749441805128, 1739757048724775633, 10244329343031345639, 284799132367263630, 11284957454566159296, 2630525959127067705, 13541892967458782500, 3947014231655981789, 14540271853602915987, 14106184675032775020, 3732582752537754684, 8378914341286366259, 8883370956189867310, 14106333818173002462, 14757226994882298819, 14499792876142316595, 12838588930199229331, 1287259937974415693, 10292084440680200055, 7666632129222600846, 17655623009184422569, 2888170709666694480, 15527639096469143275, 6148914414247297300, 12273810184460391765, 12008396873613879978, 13684160436689594981, 15846057682120484029, 15846058069495715661, 6221277427084105549, 6221276941604459925, 15820836986298144149, 15820836684097424973, 10294017242267422285, 10294017572094204696, 8641994754290998040, 8641994783654940945, 3462370327551021329, 3462370018821403635, 16782806054769521651, 16782806132588264830, 16782802834053381502, 16782803543901935745, 16710450181236136065, 16710449292177905777, 7189542811777177713, 7189543380141786822, 5598577542540609222, 5598577414253280804, 9085986405000642084, 9085986403286259585, 11574257083245664129, 11574256562975275770, 16727579601431165690, 16727580576957979518, 17657118702196087678, 17657118047375544495, 17513600993625198767, 17513600856219660495, 206375694543]]

/-- The actual candidate preferred source label. -/
def generatedAxisGlobalOddFourthSelectedSource (k : Fin 4) (j : Fin 4584) : GriessShortIndex :=
  generatedAxisGlobalOddFourthSelectedDecode (generatedAxisGlobalOddFourthSelectedSourceIndex k j)

/-- The original central correction candidate for the full inverse preferred-Q image. -/
def generatedAxisGlobalOddFourthSelectedPhase (k : Fin 4) (j : Fin 4584) : ZMod 2 :=
  if (generatedAxisGlobalOddFourthSelectedPhaseBlocks k ⟨j.val/64, by omega⟩).testBit
    (j.val%64) then 1 else 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
