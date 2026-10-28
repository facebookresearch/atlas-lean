/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete original-source equations for every H auxiliary letter in the C431 replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxE8CertificateBoundaries

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact H definitions, with every nontrivial reduction bound to a checked E8 certificate. -/
inductive Y431AuxReplayHRule
  /-- The identity word. -/
  | one
  /-- An original source generator. -/
  | generator (vertex : Fin 9)
  /-- A literal product and its exact normalization certificate. -/
  | mul (first second : Fin 620) (certificate : Fin 574)
  /-- A literal inverse and its exact normalization certificate. -/
  | inv (word : Fin 620) (certificate : Fin 574)
  /-- A literal reversed word whose inverse identity follows from the original generator squares. -/
  | reverse (word : Fin 620)

set_option maxRecDepth 100000 in
/-- The exact defining operation for each H letter used by the acyclic trace. -/
def y431AuxReplayHRule : Fin 620 → Y431AuxReplayHRule :=
![
  .generator 0
,
  .generator 1
,
  .generator 2
,
  .generator 3
,
  .generator 4
,
  .generator 5
,
  .generator 6
,
  .generator 8
,
  .mul 6 5 8
,
  .mul 8 6 9
,
  .mul 9 0 10
,
  .mul 10 5 11
,
  .mul 11 2 12
,
  .mul 12 6 13
,
  .mul 13 1 14
,
  .mul 14 7 15
,
  .mul 15 2 16
,
  .mul 16 0 17
,
  .mul 17 5 18
,
  .mul 18 1 19
,
  .mul 19 7 20
,
  .mul 20 6 21
,
  .mul 21 2 22
,
  .mul 22 0 23
,
  .mul 23 5 24
,
  .mul 24 1 25
,
  .mul 25 7 26
,
  .mul 26 2 27
,
  .mul 27 6 28
,
  .mul 28 0 29
,
  .mul 29 1 30
,
  .mul 30 7 31
,
  .mul 31 5 32
,
  .mul 32 2 33
,
  .mul 33 6 34
,
  .inv 34 35
,
  .mul 34 1 36
,
  .mul 36 35 37
,
  .inv 37 38
,
  .mul 34 2 39
,
  .mul 39 35 40
,
  .inv 40 41
,
  .mul 34 5 42
,
  .mul 42 35 43
,
  .inv 43 44
,
  .mul 34 6 45
,
  .mul 45 35 46
,
  .inv 46 47
,
  .mul 34 7 48
,
  .mul 48 35 49
,
  .inv 49 50
,
  .mul 2 35 51
,
  .mul 34 51 52
,
  .mul 3 35 53
,
  .mul 34 53 54
,
  .mul 34 0 55
,
  .inv 55 56
,
  .mul 34 56 57
,
  .inv 57 58
,
  .mul 58 52 59
,
  .mul 59 57 60
,
  .mul 58 54 61
,
  .mul 61 57 62
,
  .mul 35 57 63
,
  .mul 5 63 64
,
  .inv 63 65
,
  .mul 65 64 66
,
  .mul 6 63 67
,
  .mul 65 67 68
,
  .mul 38 57 69
,
  .inv 69 70
,
  .mul 70 57 71
,
  .reverse 62
,
  .inv 66 72
,
  .mul 73 62 73
,
  .mul 74 66 74
,
  .mul 73 58 75
,
  .mul 76 66 76
,
  .mul 68 66 77
,
  .inv 78 78
,
  .mul 79 66 79
,
  .inv 77 44
,
  .inv 80 80
,
  .mul 80 81 81
,
  .mul 83 82 82
,
  .mul 80 66 83
,
  .mul 85 82 84
,
  .inv 84 44
,
  .inv 86 47
,
  .mul 58 50 85
,
  .mul 89 57 86
,
  .mul 66 82 87
,
  .mul 60 66 88
,
  .mul 92 82 89
,
  .inv 91 78
,
  .mul 94 93 90
,
  .mul 73 90 91
,
  .mul 96 66 92
,
  .mul 73 71 93
,
  .mul 98 66 94
,
  .mul 77 73 95
,
  .mul 100 66 76
,
  .mul 101 60 96
,
  .mul 102 68 97
,
  .mul 103 58 98
,
  .mul 104 34 99
,
  .mul 105 1 100
,
  .mul 106 7 101
,
  .mul 107 2 102
,
  .mul 108 0 103
,
  .mul 109 5 104
,
  .mul 110 1 105
,
  .mul 111 7 106
,
  .mul 112 6 107
,
  .mul 113 2 108
,
  .mul 114 0 109
,
  .mul 115 5 110
,
  .mul 116 1 111
,
  .mul 117 7 112
,
  .mul 118 2 113
,
  .mul 119 6 114
,
  .mul 120 0 115
,
  .mul 121 35 116
,
  .mul 122 38 117
,
  .mul 123 50 118
,
  .mul 124 44 119
,
  .mul 125 41 120
,
  .mul 126 47 121
,
  .mul 127 57 122
,
  .mul 128 57 123
,
  .mul 129 66 124
,
  .mul 130 66 125
,
  .mul 131 82 126
,
  .mul 132 82 127
,
  .mul 133 6 128
,
  .mul 134 5 129
,
  .mul 135 6 130
,
  .mul 99 82 131
,
  .mul 80 137 132
,
  .mul 80 136 133
,
  .inv 139 134
,
  .mul 99 136 135
,
  .inv 141 136
,
  .mul 142 136 137
,
  .inv 138 138
,
  .mul 138 139 139
,
  .reverse 145
,
  .mul 140 145 140
,
  .inv 147 1
,
  .mul 7 147 141
,
  .inv 149 142
,
  .mul 150 147 143
,
  .inv 151 7
,
  .mul 80 97 144
,
  .mul 153 82 145
,
  .mul 139 147 146
,
  .mul 95 155 147
,
  .inv 156 148
,
  .mul 157 155 149
,
  .mul 154 144 150
,
  .inv 159 151
,
  .mul 160 144 152
,
  .mul 88 144 153
,
  .mul 138 162 154
,
  .inv 158 80
,
  .inv 161 155
,
  .mul 165 163 156
,
  .mul 166 161 157
,
  .mul 165 80 158
,
  .mul 168 161 159
,
  .reverse 169
,
  .mul 161 151 160
,
  .mul 171 161 161
,
  .inv 172 162
,
  .mul 172 151 163
,
  .inv 174 160
,
  .mul 175 151 164
,
  .mul 138 87 165
,
  .mul 177 144 166
,
  .mul 138 95 167
,
  .mul 179 144 168
,
  .mul 138 138 169
,
  .mul 181 88 47
,
  .mul 182 80 170
,
  .mul 183 80 84
,
  .mul 184 77 171
,
  .mul 185 73 172
,
  .mul 186 66 173
,
  .mul 187 60 174
,
  .mul 188 68 175
,
  .mul 189 58 176
,
  .mul 190 34 177
,
  .mul 191 1 178
,
  .mul 192 7 179
,
  .mul 193 2 180
,
  .mul 194 0 181
,
  .mul 195 5 182
,
  .mul 196 1 183
,
  .mul 197 7 184
,
  .mul 198 6 185
,
  .mul 199 2 186
,
  .mul 200 0 187
,
  .mul 201 5 188
,
  .mul 202 1 189
,
  .mul 203 7 190
,
  .mul 204 2 191
,
  .mul 205 6 192
,
  .mul 206 0 193
,
  .mul 207 35 194
,
  .mul 208 38 195
,
  .mul 209 50 196
,
  .mul 210 44 197
,
  .mul 211 41 198
,
  .mul 212 47 199
,
  .mul 213 57 200
,
  .mul 214 57 201
,
  .mul 215 66 202
,
  .mul 216 66 203
,
  .mul 217 82 204
,
  .mul 218 82 205
,
  .mul 219 144 206
,
  .mul 220 144 207
,
  .mul 221 161 208
,
  .mul 222 161 209
,
  .mul 223 172 210
,
  .mul 224 172 211
,
  .mul 225 151 212
,
  .mul 226 151 213
,
  .mul 227 6 214
,
  .mul 228 152 215
,
  .mul 161 138 150
,
  .mul 230 165 216
,
  .mul 229 173 217
,
  .inv 232 218
,
  .mul 232 169 219
,
  .mul 234 233 220
,
  .inv 235 6
,
  .mul 232 165 221
,
  .mul 237 229 222
,
  .inv 238 160
,
  .mul 178 161 223
,
  .mul 240 80 224
,
  .mul 241 138 225
,
  .mul 242 138 226
,
  .mul 243 88 227
,
  .mul 244 80 228
,
  .mul 245 80 229
,
  .mul 246 77 230
,
  .mul 247 73 231
,
  .mul 248 66 232
,
  .mul 249 60 233
,
  .mul 250 68 234
,
  .mul 251 58 235
,
  .mul 252 34 236
,
  .mul 253 1 237
,
  .mul 254 7 238
,
  .mul 255 2 239
,
  .mul 256 0 240
,
  .mul 257 5 241
,
  .mul 258 1 242
,
  .mul 259 7 243
,
  .mul 260 6 244
,
  .mul 261 2 245
,
  .mul 262 0 246
,
  .mul 263 5 247
,
  .mul 264 1 248
,
  .mul 265 7 249
,
  .mul 266 2 250
,
  .mul 267 6 251
,
  .mul 268 0 252
,
  .mul 269 35 253
,
  .mul 270 38 254
,
  .mul 271 50 255
,
  .mul 272 44 256
,
  .mul 273 41 257
,
  .mul 274 47 258
,
  .mul 275 57 259
,
  .mul 276 57 260
,
  .mul 277 66 261
,
  .mul 278 66 262
,
  .mul 279 82 219
,
  .mul 280 82 263
,
  .mul 281 144 264
,
  .mul 282 144 265
,
  .mul 283 161 221
,
  .mul 284 161 266
,
  .inv 285 218
,
  .mul 285 144 264
,
  .mul 287 286 267
,
  .inv 288 47
,
  .mul 238 151 268
,
  .inv 290 162
,
  .mul 147 158 269
,
  .mul 292 148 270
,
  .mul 147 176 271
,
  .mul 294 148 272
,
  .mul 144 161 273
,
  .inv 296 151
,
  .mul 289 161 274
,
  .mul 178 231 275
,
  .mul 299 289 276
,
  .mul 300 236 277
,
  .mul 301 161 278
,
  .mul 302 238 279
,
  .mul 303 173 280
,
  .mul 304 173 281
,
  .mul 305 169 282
,
  .mul 306 165 283
,
  .mul 307 165 284
,
  .mul 308 161 283
,
  .mul 309 167 285
,
  .mul 310 297 286
,
  .mul 311 144 287
,
  .mul 312 80 288
,
  .mul 313 80 289
,
  .mul 314 77 290
,
  .mul 315 97 291
,
  .mul 316 99 292
,
  .mul 317 66 293
,
  .mul 318 82 294
,
  .mul 319 82 295
,
  .mul 320 139 296
,
  .mul 321 295 297
,
  .mul 322 293 298
,
  .mul 323 5 299
,
  .mul 324 6 300
,
  .mul 325 143 301
,
  .mul 326 0 302
,
  .mul 327 5 303
,
  .mul 328 2 304
,
  .mul 329 6 305
,
  .mul 330 7 306
,
  .mul 331 0 307
,
  .mul 332 5 308
,
  .mul 333 6 309
,
  .mul 334 143 310
,
  .mul 335 0 311
,
  .mul 336 2 312
,
  .mul 337 5 313
,
  .mul 338 6 314
,
  .inv 298 315
,
  .mul 340 339 316
,
  .inv 341 317
,
  .mul 341 3 318
,
  .mul 343 342 319
,
  .inv 344 3
,
  .mul 80 75 320
,
  .mul 346 82 321
,
  .mul 148 3 322
,
  .mul 348 147 323
,
  .mul 152 173 324
,
  .mul 152 239 325
,
  .inv 351 162
,
  .mul 350 165 161
,
  .inv 353 162
,
  .mul 138 347 326
,
  .mul 355 144 327
,
  .mul 351 4 328
,
  .mul 357 352 329
,
  .mul 291 4 328
,
  .mul 359 290 329
,
  .mul 345 352 330
,
  .mul 361 351 331
,
  .reverse 362
,
  .mul 352 6 332
,
  .mul 364 351 333
,
  .inv 365 6
,
  .mul 352 164 334
,
  .mul 367 351 335
,
  .reverse 368
,
  .mul 352 147 336
,
  .mul 370 351 337
,
  .reverse 371
,
  .mul 228 351 338
,
  .reverse 373
,
  .mul 352 152 163
,
  .mul 375 4 339
,
  .mul 376 151 340
,
  .mul 377 351 329
,
  .inv 378 4
,
  .inv 356 341
,
  .mul 354 5 342
,
  .mul 381 353 343
,
  .reverse 382
,
  .mul 352 353 344
,
  .inv 384 345
,
  .mul 352 358 328
,
  .mul 386 351 329
,
  .mul 290 360 328
,
  .mul 388 291 329
,
  .mul 384 380 346
,
  .mul 390 354 347
,
  .mul 391 351 348
,
  .inv 392 341
,
  .mul 0 1 349
,
  .mul 394 5 350
,
  .mul 395 7 351
,
  .mul 396 2 352
,
  .mul 397 6 353
,
  .mul 398 3 354
,
  .mul 399 0 355
,
  .mul 400 1 356
,
  .mul 401 5 357
,
  .mul 402 7 358
,
  .mul 403 2 359
,
  .mul 404 6 360
,
  .mul 405 3 361
,
  .mul 406 0 362
,
  .mul 407 1 363
,
  .mul 408 5 364
,
  .mul 409 7 365
,
  .mul 410 2 366
,
  .mul 411 6 367
,
  .mul 412 3 368
,
  .mul 413 0 369
,
  .mul 414 1 370
,
  .mul 415 5 371
,
  .mul 416 7 372
,
  .mul 417 2 373
,
  .mul 418 6 374
,
  .mul 419 3 375
,
  .mul 420 0 376
,
  .mul 421 1 377
,
  .mul 422 5 378
,
  .mul 423 7 379
,
  .mul 424 2 380
,
  .mul 425 6 381
,
  .mul 426 3 382
,
  .mul 427 0 383
,
  .mul 428 1 384
,
  .mul 429 5 385
,
  .mul 430 7 386
,
  .mul 431 2 387
,
  .mul 432 6 388
,
  .mul 433 3 389
,
  .mul 434 0 390
,
  .mul 435 1 391
,
  .mul 436 5 392
,
  .mul 437 7 393
,
  .mul 438 2 394
,
  .mul 439 6 395
,
  .mul 440 3 396
,
  .mul 441 0 397
,
  .mul 442 1 398
,
  .mul 443 5 399
,
  .mul 444 7 400
,
  .mul 445 2 401
,
  .mul 446 6 402
,
  .mul 447 3 403
,
  .mul 448 0 404
,
  .mul 449 1 405
,
  .mul 450 5 406
,
  .mul 451 7 407
,
  .mul 452 2 408
,
  .mul 453 6 409
,
  .mul 454 3 410
,
  .mul 455 4 411
,
  .mul 456 0 412
,
  .mul 457 1 413
,
  .mul 458 5 414
,
  .mul 459 7 415
,
  .mul 460 2 416
,
  .mul 461 6 417
,
  .mul 462 3 418
,
  .mul 463 0 419
,
  .mul 464 1 420
,
  .mul 465 5 421
,
  .mul 466 7 422
,
  .mul 467 2 423
,
  .mul 468 6 424
,
  .mul 469 3 425
,
  .mul 470 0 426
,
  .mul 471 1 427
,
  .mul 472 5 428
,
  .mul 473 7 429
,
  .mul 474 2 430
,
  .mul 475 6 431
,
  .mul 476 3 432
,
  .mul 477 0 433
,
  .mul 478 1 434
,
  .mul 479 5 435
,
  .mul 480 7 436
,
  .mul 481 2 437
,
  .mul 482 6 438
,
  .mul 483 3 439
,
  .mul 484 0 440
,
  .mul 485 1 441
,
  .mul 486 5 442
,
  .mul 487 7 443
,
  .mul 488 2 444
,
  .mul 489 6 445
,
  .mul 490 3 446
,
  .mul 491 0 447
,
  .mul 492 1 448
,
  .mul 493 5 449
,
  .mul 494 7 450
,
  .mul 495 2 451
,
  .mul 496 6 452
,
  .mul 497 3 453
,
  .mul 498 0 454
,
  .mul 499 1 455
,
  .mul 500 5 456
,
  .mul 501 7 457
,
  .mul 502 2 458
,
  .mul 503 6 459
,
  .mul 504 3 460
,
  .mul 505 0 461
,
  .mul 506 1 462
,
  .mul 507 5 463
,
  .mul 508 7 464
,
  .mul 509 2 465
,
  .mul 510 6 466
,
  .mul 511 3 467
,
  .mul 512 0 468
,
  .mul 513 1 469
,
  .mul 514 5 470
,
  .mul 515 7 471
,
  .mul 516 2 472
,
  .mul 517 6 473
,
  .mul 518 3 474
,
  .mul 519 4 475
,
  .mul 520 0 476
,
  .mul 521 1 477
,
  .mul 522 5 478
,
  .mul 523 7 479
,
  .mul 524 2 480
,
  .mul 525 6 481
,
  .mul 526 3 482
,
  .mul 527 0 483
,
  .mul 528 1 484
,
  .mul 529 5 485
,
  .mul 530 7 486
,
  .mul 531 2 487
,
  .mul 532 6 488
,
  .mul 533 3 489
,
  .mul 534 0 490
,
  .mul 535 1 491
,
  .mul 536 5 492
,
  .mul 537 7 493
,
  .mul 538 2 494
,
  .mul 539 6 495
,
  .mul 540 3 496
,
  .mul 541 0 497
,
  .mul 542 1 498
,
  .mul 543 5 499
,
  .mul 544 7 500
,
  .mul 545 2 501
,
  .mul 546 6 502
,
  .mul 547 3 503
,
  .mul 548 0 504
,
  .mul 549 1 505
,
  .mul 550 5 506
,
  .mul 551 7 507
,
  .mul 552 2 508
,
  .mul 553 6 509
,
  .mul 554 3 510
,
  .mul 555 0 511
,
  .mul 556 1 512
,
  .mul 557 5 513
,
  .mul 558 7 514
,
  .mul 559 2 515
,
  .mul 560 6 516
,
  .mul 561 3 517
,
  .mul 562 0 518
,
  .mul 563 1 519
,
  .mul 564 5 520
,
  .mul 565 7 521
,
  .mul 566 2 522
,
  .mul 567 6 523
,
  .mul 568 3 524
,
  .mul 569 0 525
,
  .mul 570 1 526
,
  .mul 571 5 527
,
  .mul 572 7 528
,
  .mul 573 2 529
,
  .mul 574 6 530
,
  .mul 575 3 531
,
  .mul 576 0 532
,
  .mul 577 1 533
,
  .mul 578 5 534
,
  .mul 579 7 535
,
  .mul 580 2 536
,
  .mul 581 6 537
,
  .mul 582 3 538
,
  .mul 583 4 539
,
  .mul 373 379 540
,
  .mul 585 368 541
,
  .mul 586 365 542
,
  .mul 587 362 543
,
  .mul 588 371 544
,
  .mul 589 393 545
,
  .mul 590 352 546
,
  .mul 591 351 547
,
  .mul 592 366 548
,
  .mul 593 387 549
,
  .mul 594 80 550
,
  .mul 595 380 551
,
  .mul 596 382 552
,
  .mul 597 362 553
,
  .mul 598 4 554
,
  .mul 599 180 555
,
  .mul 600 380 556
,
  .mul 601 80 557
,
  .mul 602 389 558
,
  .mul 603 290 559
,
  .mul 604 147 560
,
  .mul 605 349 561
,
  .mul 606 158 562
,
  .mul 607 6 563
,
  .mul 608 4 564
,
  .mul 609 5 565
,
  .mul 610 147 566
,
  .mul 611 349 567
,
  .mul 612 6 568
,
  .mul 613 4 569
,
  .mul 614 353 570
,
  .mul 615 385 571
,
  .mul 616 352 572
,
  .mul 617 353 570
,
  .mul 618 380 573
]

/-- Bind the proposed H operation to the actual literal boundaries of its checked certificate. -/
def y431AuxReplayHRuleChecked (i : Fin 620) : Prop :=
  match y431AuxReplayHRule i with
  | .one => y431AuxReplayHWord i = []
  | .generator v => y431AuxReplayHWord i = [v]
  | .mul a b c =>
    y431AuxE8CertificateBoundary c 0 = y431AuxReplayHWord a ++ y431AuxReplayHWord b ∧
      y431AuxE8CertificateBoundary c (Fin.last (y431AuxE8CertificateLength c)) =
        y431AuxReplayHWord i
  | .inv a c =>
    y431AuxE8CertificateBoundary c 0 = (y431AuxReplayHWord a).reverse ∧
      y431AuxE8CertificateBoundary c (Fin.last (y431AuxE8CertificateLength c)) =
        y431AuxReplayHWord i
  | .reverse a => y431AuxReplayHWord i = (y431AuxReplayHWord a).reverse

/-- Every literal operation-boundary comparison is decidable. -/
instance y431AuxReplayHRuleCheckedDecidable (i : Fin 620) :
    Decidable (y431AuxReplayHRuleChecked i) := by
  unfold y431AuxReplayHRuleChecked
  split <;> infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
