/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete source-kind and auxiliary-path definitions for the original C431 replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplaySymbols
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayHRuleConsequences

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A trace path is the empty word or a previously assigned literal path followed by one symbol. -/
inductive Y431AuxReplayTDefinition
  /-- The original empty auxiliary path. -/
  | one
  /-- The declared literal prefix and its appended original-source symbol. -/
  | append (previous : Fin 180) (generator : Fin 10)

set_option maxRecDepth 100000 in
/-- The literal path-defining operation for every T symbol used by the exact replay. -/
def y431AuxReplayTDefinition : Fin 180 → Y431AuxReplayTDefinition :=
![
  .one
,
  .append 0 7
,
  .append 1 6
,
  .append 0 9
,
  .append 3 7
,
  .append 4 6
,
  .append 5 5
,
  .append 6 0
,
  .append 7 8
,
  .append 8 1
,
  .append 9 0
,
  .append 10 2
,
  .append 11 8
,
  .append 12 1
,
  .append 13 5
,
  .append 14 0
,
  .append 15 2
,
  .append 16 6
,
  .append 17 8
,
  .append 18 1
,
  .append 19 5
,
  .append 20 0
,
  .append 21 7
,
  .append 22 2
,
  .append 23 6
,
  .append 24 8
,
  .append 25 1
,
  .append 26 5
,
  .append 27 0
,
  .append 28 7
,
  .append 29 2
,
  .append 30 6
,
  .append 31 8
,
  .append 32 1
,
  .append 33 5
,
  .append 34 0
,
  .append 33 8
,
  .append 30 0
,
  .append 27 1
,
  .append 24 0
,
  .append 39 6
,
  .append 40 8
,
  .append 41 5
,
  .append 42 0
,
  .append 43 7
,
  .append 14 1
,
  .append 11 0
,
  .append 9 8
,
  .append 47 2
,
  .append 37 5
,
  .append 26 6
,
  .append 20 8
,
  .append 43 1
,
  .append 52 7
,
  .append 53 2
,
  .append 54 6
,
  .append 11 3
,
  .append 13 3
,
  .append 57 2
,
  .append 57 4
,
  .append 57 5
,
  .append 18 6
,
  .append 52 2
,
  .append 15 3
,
  .append 60 2
,
  .append 60 4
,
  .append 60 6
,
  .append 24 3
,
  .append 63 2
,
  .append 63 4
,
  .append 63 6
,
  .append 63 8
,
  .append 39 3
,
  .append 70 2
,
  .append 70 5
,
  .append 70 7
,
  .append 70 8
,
  .append 40 3
,
  .append 76 2
,
  .append 76 5
,
  .append 41 3
,
  .append 79 2
,
  .append 43 3
,
  .append 26 3
,
  .append 67 2
,
  .append 72 2
,
  .append 72 4
,
  .append 77 2
,
  .append 77 4
,
  .append 80 2
,
  .append 80 4
,
  .append 75 2
,
  .append 75 4
,
  .append 52 3
,
  .append 82 2
,
  .append 82 4
,
  .append 66 4
,
  .append 74 2
,
  .append 89 1
,
  .append 98 5
,
  .append 99 7
,
  .append 100 6
,
  .append 101 8
,
  .append 102 1
,
  .append 89 6
,
  .append 85 1
,
  .append 105 6
,
  .append 58 4
,
  .append 91 8
,
  .append 108 1
,
  .append 106 7
,
  .append 110 8
,
  .append 86 2
,
  .append 112 6
,
  .append 113 8
,
  .append 114 1
,
  .append 115 5
,
  .append 116 7
,
  .append 117 6
,
  .append 118 8
,
  .append 119 1
,
  .append 120 2
,
  .append 114 6
,
  .append 112 1
,
  .append 123 6
,
  .append 114 5
,
  .append 125 0
,
  .append 126 7
,
  .append 78 1
,
  .append 107 3
,
  .append 107 5
,
  .append 125 8
,
  .append 131 1
,
  .append 124 7
,
  .append 133 8
,
  .append 134 1
,
  .append 135 5
,
  .append 68 4
,
  .append 130 3
,
  .append 120 6
,
  .append 134 0
,
  .append 140 7
,
  .append 137 3
,
  .append 136 3
,
  .append 128 4
,
  .append 139 3
,
  .append 119 0
,
  .append 112 3
,
  .append 114 3
,
  .append 125 3
,
  .append 126 3
,
  .append 127 3
,
  .append 115 3
,
  .append 116 3
,
  .append 117 3
,
  .append 118 3
,
  .append 119 3
,
  .append 120 3
,
  .append 123 3
,
  .append 124 3
,
  .append 132 3
,
  .append 133 3
,
  .append 134 3
,
  .append 141 3
,
  .append 152 2
,
  .append 144 3
,
  .append 153 2
,
  .append 154 2
,
  .append 155 2
,
  .append 146 3
,
  .append 156 2
,
  .append 158 2
,
  .append 159 2
,
  .append 170 0
,
  .append 169 6
,
  .append 160 2
,
  .append 164 0
,
  .append 176 7
,
  .append 177 2
,
  .append 164 6
]

/-- Compare each declared T definition with its actual literal path word. -/
def y431AuxReplayTDefinitionChecked (i : Fin 180) : Prop :=
  match y431AuxReplayTDefinition i with
  | .one => y431AuxReplayTWord i = []
  | .append a g => y431AuxReplayTWord i = y431AuxReplayTWord a ++ [g]

/-- Exact finite comparison of literal auxiliary path definitions is decidable. -/
instance y431AuxReplayTDefinitionCheckedDecidable (i : Fin 180) :
    Decidable (y431AuxReplayTDefinitionChecked i) := by
  unfold y431AuxReplayTDefinitionChecked
  split <;> infer_instance

/-- Every source is an original proved square or relator, or an explicit actual word definition. -/
inductive Y431AuxReplaySourceKind
  /-- A proved original or redundant-symbol involution relation. -/
  | square (generator : Fin 10)
  /-- An exact original or already derived relator. -/
  | relator (relator : Fin 46)
  /-- An actual H word definition proved by the checked Coxeter certificates. -/
  | H (word : Fin 620)
  /-- An explicit T path definition. -/
  | T (word : Fin 180)

set_option maxRecDepth 100000 in
/-- Number every concrete source equation in the same order as the original acyclic trace. -/
def y431AuxReplaySourceKind : Fin 856 → Y431AuxReplaySourceKind :=
![
  .T 1
,
  .T 0
,
  .square 7
,
  .relator 6
,
  .square 0
,
  .relator 13
,
  .square 1
,
  .relator 19
,
  .square 2
,
  .relator 24
,
  .square 3
,
  .relator 28
,
  .square 4
,
  .relator 31
,
  .square 5
,
  .relator 35
,
  .square 8
,
  .T 2
,
  .square 6
,
  .relator 5
,
  .relator 12
,
  .relator 18
,
  .relator 23
,
  .relator 27
,
  .relator 33
,
  .relator 34
,
  .T 3
,
  .square 9
,
  .relator 37
,
  .relator 38
,
  .relator 39
,
  .relator 40
,
  .relator 41
,
  .relator 42
,
  .relator 43
,
  .relator 45
,
  .T 4
,
  .relator 44
,
  .T 5
,
  .T 6
,
  .relator 11
,
  .relator 17
,
  .relator 22
,
  .relator 26
,
  .relator 30
,
  .relator 32
,
  .T 7
,
  .relator 1
,
  .relator 2
,
  .relator 3
,
  .relator 4
,
  .T 8
,
  .relator 7
,
  .relator 20
,
  .relator 25
,
  .relator 29
,
  .T 9
,
  .relator 9
,
  .relator 10
,
  .T 10
,
  .relator 0
,
  .T 11
,
  .relator 16
,
  .T 12
,
  .T 13
,
  .T 14
,
  .T 15
,
  .T 16
,
  .T 17
,
  .T 18
,
  .T 19
,
  .T 20
,
  .T 21
,
  .T 22
,
  .T 23
,
  .T 24
,
  .T 25
,
  .T 26
,
  .T 27
,
  .T 28
,
  .T 29
,
  .T 30
,
  .T 31
,
  .T 32
,
  .T 33
,
  .T 34
,
  .T 35
,
  .H 8
,
  .H 6
,
  .H 5
,
  .H 9
,
  .H 10
,
  .H 0
,
  .H 11
,
  .H 12
,
  .H 2
,
  .H 13
,
  .H 14
,
  .H 1
,
  .H 15
,
  .H 7
,
  .H 16
,
  .H 17
,
  .H 18
,
  .H 19
,
  .H 20
,
  .H 21
,
  .H 22
,
  .H 23
,
  .H 24
,
  .H 25
,
  .H 26
,
  .H 27
,
  .H 28
,
  .H 29
,
  .H 30
,
  .H 31
,
  .H 32
,
  .H 33
,
  .H 34
,
  .relator 36
,
  .H 35
,
  .H 36
,
  .H 37
,
  .H 38
,
  .H 39
,
  .H 40
,
  .H 41
,
  .H 3
,
  .H 42
,
  .H 43
,
  .H 44
,
  .H 45
,
  .H 46
,
  .H 47
,
  .H 48
,
  .H 49
,
  .H 50
,
  .H 51
,
  .H 52
,
  .H 53
,
  .H 54
,
  .H 55
,
  .H 56
,
  .H 57
,
  .H 58
,
  .H 59
,
  .H 60
,
  .H 61
,
  .H 62
,
  .H 63
,
  .H 64
,
  .H 65
,
  .H 66
,
  .H 67
,
  .H 68
,
  .H 69
,
  .H 70
,
  .H 71
,
  .H 72
,
  .H 73
,
  .H 74
,
  .H 75
,
  .H 76
,
  .H 77
,
  .H 78
,
  .H 79
,
  .H 80
,
  .H 81
,
  .H 82
,
  .H 83
,
  .H 84
,
  .H 85
,
  .H 86
,
  .H 87
,
  .H 88
,
  .T 36
,
  .H 89
,
  .H 90
,
  .relator 14
,
  .H 91
,
  .H 92
,
  .H 93
,
  .relator 8
,
  .H 94
,
  .H 95
,
  .T 37
,
  .H 96
,
  .H 97
,
  .H 98
,
  .H 99
,
  .H 100
,
  .H 101
,
  .H 102
,
  .H 103
,
  .H 104
,
  .H 105
,
  .H 106
,
  .H 107
,
  .H 108
,
  .H 109
,
  .H 110
,
  .H 111
,
  .H 112
,
  .H 113
,
  .H 114
,
  .H 115
,
  .H 116
,
  .H 117
,
  .H 118
,
  .H 119
,
  .H 120
,
  .H 121
,
  .H 122
,
  .H 123
,
  .H 124
,
  .H 125
,
  .H 126
,
  .H 127
,
  .H 128
,
  .H 129
,
  .H 130
,
  .H 131
,
  .H 132
,
  .H 133
,
  .H 134
,
  .H 135
,
  .H 136
,
  .H 137
,
  .H 138
,
  .H 139
,
  .H 140
,
  .H 141
,
  .H 142
,
  .H 143
,
  .H 144
,
  .H 145
,
  .H 146
,
  .H 147
,
  .H 148
,
  .H 149
,
  .H 150
,
  .H 151
,
  .H 152
,
  .T 38
,
  .H 153
,
  .H 154
,
  .H 155
,
  .H 156
,
  .H 157
,
  .H 158
,
  .H 159
,
  .H 160
,
  .H 161
,
  .H 162
,
  .H 163
,
  .H 164
,
  .H 165
,
  .H 166
,
  .H 167
,
  .H 168
,
  .H 169
,
  .H 170
,
  .H 171
,
  .H 172
,
  .H 173
,
  .H 174
,
  .H 175
,
  .H 176
,
  .T 39
,
  .H 177
,
  .H 178
,
  .H 179
,
  .H 180
,
  .H 181
,
  .H 182
,
  .H 183
,
  .H 184
,
  .H 185
,
  .H 186
,
  .H 187
,
  .H 188
,
  .H 189
,
  .H 190
,
  .H 191
,
  .H 192
,
  .H 193
,
  .H 194
,
  .H 195
,
  .H 196
,
  .H 197
,
  .H 198
,
  .H 199
,
  .H 200
,
  .H 201
,
  .H 202
,
  .H 203
,
  .H 204
,
  .H 205
,
  .H 206
,
  .H 207
,
  .H 208
,
  .H 209
,
  .H 210
,
  .H 211
,
  .H 212
,
  .H 213
,
  .H 214
,
  .H 215
,
  .H 216
,
  .H 217
,
  .H 218
,
  .H 219
,
  .H 220
,
  .H 221
,
  .H 222
,
  .H 223
,
  .H 224
,
  .H 225
,
  .H 226
,
  .H 227
,
  .H 228
,
  .T 40
,
  .H 229
,
  .T 41
,
  .H 230
,
  .H 231
,
  .T 42
,
  .H 232
,
  .H 233
,
  .H 234
,
  .H 235
,
  .H 236
,
  .H 237
,
  .H 238
,
  .H 239
,
  .T 43
,
  .H 240
,
  .H 241
,
  .H 242
,
  .H 243
,
  .H 244
,
  .H 245
,
  .H 246
,
  .H 247
,
  .H 248
,
  .H 249
,
  .H 250
,
  .H 251
,
  .H 252
,
  .H 253
,
  .H 254
,
  .H 255
,
  .H 256
,
  .H 257
,
  .H 258
,
  .H 259
,
  .H 260
,
  .H 261
,
  .H 262
,
  .H 263
,
  .H 264
,
  .H 265
,
  .H 266
,
  .H 267
,
  .H 268
,
  .H 269
,
  .H 270
,
  .H 271
,
  .H 272
,
  .H 273
,
  .H 274
,
  .H 275
,
  .H 276
,
  .H 277
,
  .H 278
,
  .H 279
,
  .H 280
,
  .H 281
,
  .H 282
,
  .H 283
,
  .H 284
,
  .H 285
,
  .H 286
,
  .H 287
,
  .H 288
,
  .H 289
,
  .T 44
,
  .H 290
,
  .H 291
,
  .T 45
,
  .T 46
,
  .H 292
,
  .H 293
,
  .H 294
,
  .H 295
,
  .T 47
,
  .T 48
,
  .T 49
,
  .T 50
,
  .H 296
,
  .H 297
,
  .T 51
,
  .T 52
,
  .T 53
,
  .T 54
,
  .T 55
,
  .H 298
,
  .H 299
,
  .H 300
,
  .H 301
,
  .H 302
,
  .H 303
,
  .H 304
,
  .H 305
,
  .H 306
,
  .H 307
,
  .H 308
,
  .H 309
,
  .H 310
,
  .H 311
,
  .H 312
,
  .H 313
,
  .H 314
,
  .H 315
,
  .H 316
,
  .H 317
,
  .H 318
,
  .H 319
,
  .H 320
,
  .H 321
,
  .H 322
,
  .H 323
,
  .H 324
,
  .H 325
,
  .H 326
,
  .H 327
,
  .H 328
,
  .H 329
,
  .H 330
,
  .H 331
,
  .H 332
,
  .H 333
,
  .H 334
,
  .H 335
,
  .H 336
,
  .H 337
,
  .H 338
,
  .H 339
,
  .H 340
,
  .H 341
,
  .H 342
,
  .H 343
,
  .H 344
,
  .H 345
,
  .relator 15
,
  .T 56
,
  .T 57
,
  .relator 21
,
  .H 346
,
  .H 347
,
  .T 58
,
  .H 348
,
  .H 349
,
  .T 59
,
  .T 60
,
  .T 61
,
  .T 62
,
  .T 63
,
  .T 64
,
  .T 65
,
  .T 66
,
  .T 67
,
  .T 68
,
  .T 69
,
  .T 70
,
  .T 71
,
  .T 72
,
  .T 73
,
  .H 4
,
  .T 74
,
  .H 350
,
  .T 75
,
  .H 351
,
  .H 352
,
  .T 76
,
  .T 77
,
  .T 78
,
  .T 79
,
  .H 353
,
  .H 354
,
  .T 80
,
  .T 81
,
  .T 82
,
  .T 83
,
  .T 84
,
  .H 355
,
  .H 356
,
  .T 85
,
  .T 86
,
  .T 87
,
  .T 88
,
  .T 89
,
  .T 90
,
  .T 91
,
  .T 92
,
  .H 357
,
  .H 358
,
  .T 93
,
  .T 94
,
  .T 95
,
  .T 96
,
  .H 359
,
  .H 360
,
  .T 97
,
  .T 98
,
  .T 99
,
  .H 361
,
  .H 362
,
  .H 363
,
  .H 364
,
  .H 365
,
  .H 366
,
  .T 100
,
  .T 101
,
  .H 367
,
  .H 368
,
  .H 369
,
  .T 102
,
  .T 103
,
  .H 370
,
  .H 371
,
  .H 372
,
  .T 104
,
  .T 105
,
  .H 373
,
  .H 374
,
  .T 106
,
  .T 107
,
  .T 108
,
  .T 109
,
  .T 110
,
  .T 111
,
  .T 112
,
  .T 113
,
  .T 114
,
  .T 115
,
  .T 116
,
  .T 117
,
  .T 118
,
  .T 119
,
  .T 120
,
  .T 121
,
  .H 375
,
  .H 376
,
  .H 377
,
  .H 378
,
  .H 379
,
  .T 122
,
  .T 123
,
  .H 380
,
  .T 124
,
  .T 125
,
  .T 126
,
  .T 127
,
  .T 128
,
  .T 129
,
  .T 130
,
  .T 131
,
  .T 132
,
  .T 133
,
  .T 134
,
  .T 135
,
  .H 381
,
  .H 382
,
  .H 383
,
  .T 136
,
  .T 137
,
  .T 138
,
  .T 139
,
  .H 384
,
  .H 385
,
  .T 140
,
  .T 141
,
  .T 142
,
  .T 143
,
  .T 144
,
  .T 145
,
  .T 146
,
  .T 147
,
  .T 148
,
  .T 149
,
  .H 386
,
  .H 387
,
  .T 150
,
  .T 151
,
  .H 388
,
  .H 389
,
  .T 152
,
  .T 153
,
  .T 154
,
  .T 155
,
  .T 156
,
  .T 157
,
  .T 158
,
  .T 159
,
  .T 160
,
  .T 161
,
  .T 162
,
  .T 163
,
  .T 164
,
  .T 165
,
  .T 166
,
  .T 167
,
  .T 168
,
  .T 169
,
  .T 170
,
  .T 171
,
  .T 172
,
  .T 173
,
  .T 174
,
  .H 390
,
  .H 391
,
  .H 392
,
  .H 393
,
  .T 175
,
  .T 176
,
  .T 177
,
  .T 178
,
  .T 179
,
  .H 394
,
  .H 395
,
  .H 396
,
  .H 397
,
  .H 398
,
  .H 399
,
  .H 400
,
  .H 401
,
  .H 402
,
  .H 403
,
  .H 404
,
  .H 405
,
  .H 406
,
  .H 407
,
  .H 408
,
  .H 409
,
  .H 410
,
  .H 411
,
  .H 412
,
  .H 413
,
  .H 414
,
  .H 415
,
  .H 416
,
  .H 417
,
  .H 418
,
  .H 419
,
  .H 420
,
  .H 421
,
  .H 422
,
  .H 423
,
  .H 424
,
  .H 425
,
  .H 426
,
  .H 427
,
  .H 428
,
  .H 429
,
  .H 430
,
  .H 431
,
  .H 432
,
  .H 433
,
  .H 434
,
  .H 435
,
  .H 436
,
  .H 437
,
  .H 438
,
  .H 439
,
  .H 440
,
  .H 441
,
  .H 442
,
  .H 443
,
  .H 444
,
  .H 445
,
  .H 446
,
  .H 447
,
  .H 448
,
  .H 449
,
  .H 450
,
  .H 451
,
  .H 452
,
  .H 453
,
  .H 454
,
  .H 455
,
  .H 456
,
  .H 457
,
  .H 458
,
  .H 459
,
  .H 460
,
  .H 461
,
  .H 462
,
  .H 463
,
  .H 464
,
  .H 465
,
  .H 466
,
  .H 467
,
  .H 468
,
  .H 469
,
  .H 470
,
  .H 471
,
  .H 472
,
  .H 473
,
  .H 474
,
  .H 475
,
  .H 476
,
  .H 477
,
  .H 478
,
  .H 479
,
  .H 480
,
  .H 481
,
  .H 482
,
  .H 483
,
  .H 484
,
  .H 485
,
  .H 486
,
  .H 487
,
  .H 488
,
  .H 489
,
  .H 490
,
  .H 491
,
  .H 492
,
  .H 493
,
  .H 494
,
  .H 495
,
  .H 496
,
  .H 497
,
  .H 498
,
  .H 499
,
  .H 500
,
  .H 501
,
  .H 502
,
  .H 503
,
  .H 504
,
  .H 505
,
  .H 506
,
  .H 507
,
  .H 508
,
  .H 509
,
  .H 510
,
  .H 511
,
  .H 512
,
  .H 513
,
  .H 514
,
  .H 515
,
  .H 516
,
  .H 517
,
  .H 518
,
  .H 519
,
  .H 520
,
  .H 521
,
  .H 522
,
  .H 523
,
  .H 524
,
  .H 525
,
  .H 526
,
  .H 527
,
  .H 528
,
  .H 529
,
  .H 530
,
  .H 531
,
  .H 532
,
  .H 533
,
  .H 534
,
  .H 535
,
  .H 536
,
  .H 537
,
  .H 538
,
  .H 539
,
  .H 540
,
  .H 541
,
  .H 542
,
  .H 543
,
  .H 544
,
  .H 545
,
  .H 546
,
  .H 547
,
  .H 548
,
  .H 549
,
  .H 550
,
  .H 551
,
  .H 552
,
  .H 553
,
  .H 554
,
  .H 555
,
  .H 556
,
  .H 557
,
  .H 558
,
  .H 559
,
  .H 560
,
  .H 561
,
  .H 562
,
  .H 563
,
  .H 564
,
  .H 565
,
  .H 566
,
  .H 567
,
  .H 568
,
  .H 569
,
  .H 570
,
  .H 571
,
  .H 572
,
  .H 573
,
  .H 574
,
  .H 575
,
  .H 576
,
  .H 577
,
  .H 578
,
  .H 579
,
  .H 580
,
  .H 581
,
  .H 582
,
  .H 583
,
  .H 584
,
  .H 585
,
  .H 586
,
  .H 587
,
  .H 588
,
  .H 589
,
  .H 590
,
  .H 591
,
  .H 592
,
  .H 593
,
  .H 594
,
  .H 595
,
  .H 596
,
  .H 597
,
  .H 598
,
  .H 599
,
  .H 600
,
  .H 601
,
  .H 602
,
  .H 603
,
  .H 604
,
  .H 605
,
  .H 606
,
  .H 607
,
  .H 608
,
  .H 609
,
  .H 610
,
  .H 611
,
  .H 612
,
  .H 613
,
  .H 614
,
  .H 615
,
  .H 616
,
  .H 617
,
  .H 618
,
  .H 619
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
