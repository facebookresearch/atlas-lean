/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite coefficient lookup charts for the actual first Norton line-word tensor columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSparseLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The explicit 128-coordinate input catalogue in binary-parameter order. -/
def monsterNortonLine01CompactInputLabel (p : Fin 128) : Fin 4096 :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3561
              else
                3560
            else
              if p.val.testBit 0 then
                3559
              else
                3558
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3515
              else
                3514
            else
              if p.val.testBit 0 then
                3509
              else
                3508
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3421
              else
                3420
            else
              if p.val.testBit 0 then
                3411
              else
                3410
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3343
              else
                3342
            else
              if p.val.testBit 0 then
                3329
              else
                3328
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3305
              else
                3304
            else
              if p.val.testBit 0 then
                3303
              else
                3302
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3259
              else
                3258
            else
              if p.val.testBit 0 then
                3253
              else
                3252
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3165
              else
                3164
            else
              if p.val.testBit 0 then
                3155
              else
                3154
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3087
              else
                3086
            else
              if p.val.testBit 0 then
                3073
              else
                3072
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2537
              else
                2536
            else
              if p.val.testBit 0 then
                2535
              else
                2534
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2491
              else
                2490
            else
              if p.val.testBit 0 then
                2485
              else
                2484
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2397
              else
                2396
            else
              if p.val.testBit 0 then
                2387
              else
                2386
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2319
              else
                2318
            else
              if p.val.testBit 0 then
                2305
              else
                2304
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2281
              else
                2280
            else
              if p.val.testBit 0 then
                2279
              else
                2278
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2235
              else
                2234
            else
              if p.val.testBit 0 then
                2229
              else
                2228
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2141
              else
                2140
            else
              if p.val.testBit 0 then
                2131
              else
                2130
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2063
              else
                2062
            else
              if p.val.testBit 0 then
                2049
              else
                2048
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1513
              else
                1512
            else
              if p.val.testBit 0 then
                1511
              else
                1510
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1467
              else
                1466
            else
              if p.val.testBit 0 then
                1461
              else
                1460
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1373
              else
                1372
            else
              if p.val.testBit 0 then
                1363
              else
                1362
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1295
              else
                1294
            else
              if p.val.testBit 0 then
                1281
              else
                1280
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1257
              else
                1256
            else
              if p.val.testBit 0 then
                1255
              else
                1254
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1211
              else
                1210
            else
              if p.val.testBit 0 then
                1205
              else
                1204
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1117
              else
                1116
            else
              if p.val.testBit 0 then
                1107
              else
                1106
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1039
              else
                1038
            else
              if p.val.testBit 0 then
                1025
              else
                1024
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                489
              else
                488
            else
              if p.val.testBit 0 then
                487
              else
                486
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                443
              else
                442
            else
              if p.val.testBit 0 then
                437
              else
                436
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                349
              else
                348
            else
              if p.val.testBit 0 then
                339
              else
                338
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                271
              else
                270
            else
              if p.val.testBit 0 then
                257
              else
                256
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                233
              else
                232
            else
              if p.val.testBit 0 then
                231
              else
                230
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                187
              else
                186
            else
              if p.val.testBit 0 then
                181
              else
                180
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                93
              else
                92
            else
              if p.val.testBit 0 then
                83
              else
                82
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                15
              else
                14
            else
              if p.val.testBit 0 then
                1
              else
                0

/-- An explicit seven-coordinate inverse lookup for the input catalogue. -/
def monsterNortonLine01CompactInputLookup (n : Fin 4096) : Fin 128 :=
  ⟨(((if n.val.testBit 0 then 1 else 0) +
      (if n.val.testBit 3 then 2 else 0) +
      (if n.val.testBit 6 then 4 else 0) +
      (if n.val.testBit 7 then 8 else 0) +
      (if n.val.testBit 8 then 16 else 0) +
      (if n.val.testBit 10 then 32 else 0) +
      (if n.val.testBit 11 then 64 else 0)) % 128), Nat.mod_lt _ (by norm_num)⟩

/-- The exact membership test for the specified input support catalogue. -/
def monsterNortonLine01CompactInputSupport (n : Fin 4096) : Prop :=
  monsterNortonLine01CompactInputLabel (monsterNortonLine01CompactInputLookup n) = n

/-- The catalogue support is decided by finite index equality. -/
instance : DecidablePred monsterNortonLine01CompactInputSupport := fun n =>
  inferInstanceAs (Decidable
    (monsterNortonLine01CompactInputLabel (monsterNortonLine01CompactInputLookup n) = n))

set_option maxRecDepth 10000 in
/-- Every catalogue coordinate is recovered by its explicit inverse lookup. -/
theorem monsterNortonLine01CompactInputLookup_label (p : Fin 128) :
    monsterNortonLine01CompactInputLookup (monsterNortonLine01CompactInputLabel p) = p := by
  revert p
  decide +kernel

/-- Every displayed coordinate satisfies the exact support predicate. -/
theorem monsterNortonLine01CompactInputLabel_support (p : Fin 128) :
    monsterNortonLine01CompactInputSupport (monsterNortonLine01CompactInputLabel p) := by
  unfold monsterNortonLine01CompactInputSupport
  rw [monsterNortonLine01CompactInputLookup_label]

/-- The signed input coefficients in the specified physical-column order. -/
def monsterNortonLine01CompactInputCoefficient (k : Fin 16) (p : Fin 128) : ℤ :=
  if k.val.testBit 3 then
    if k.val.testBit 2 then
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
    else
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
  else
    if k.val.testBit 2 then
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
    else
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        1
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        1
                      else
                        (-1)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-1)
                      else
                        1
                    else
                      if p.val.testBit 0 then
                        (-1)
                      else
                        (-1)

/-- The entire integer vector evaluated by the supported coefficient lookup. -/
def monsterNortonLine01CompactInputVector (k : Fin 16) : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactInputCoefficient k (monsterNortonLine01CompactInputLookup n)
  else 0

/-- The coefficient lookup equals its explicit sparse sum as an entire integer vector. -/
theorem monsterNortonLine01CompactInputVector_sparse (k : Fin 16) :
    monsterNortonLine01CompactInputVector k =
      ∑ p : Fin 128, monsterNortonLine01CompactInputCoefficient k p •
        (Pi.single (monsterNortonLine01CompactInputLabel p) 1 : NortonUIntegerVector) := by
  exact (monsterNortonSparseLookup_eq monsterNortonLine01CompactInputLabel
    monsterNortonLine01CompactInputLookup monsterNortonLine01CompactInputSupport
    monsterNortonLine01CompactInputLookup_label monsterNortonLine01CompactInputLabel_support
    (fun n hn => hn) (monsterNortonLine01CompactInputCoefficient k)).symm

/-- The explicit 128-coordinate output catalogue in binary-parameter order. -/
def monsterNortonLine01CompactOutputLabel (p : Fin 128) : Fin 4096 :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                4095
              else
                4094
            else
              if p.val.testBit 0 then
                4093
              else
                4092
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                4083
              else
                4082
            else
              if p.val.testBit 0 then
                4081
              else
                4080
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3759
              else
                3758
            else
              if p.val.testBit 0 then
                3757
              else
                3756
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3747
              else
                3746
            else
              if p.val.testBit 0 then
                3745
              else
                3744
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3423
              else
                3422
            else
              if p.val.testBit 0 then
                3421
              else
                3420
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3411
              else
                3410
            else
              if p.val.testBit 0 then
                3409
              else
                3408
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3087
              else
                3086
            else
              if p.val.testBit 0 then
                3085
              else
                3084
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3075
              else
                3074
            else
              if p.val.testBit 0 then
                3073
              else
                3072
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3071
              else
                3070
            else
              if p.val.testBit 0 then
                3069
              else
                3068
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3059
              else
                3058
            else
              if p.val.testBit 0 then
                3057
              else
                3056
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2735
              else
                2734
            else
              if p.val.testBit 0 then
                2733
              else
                2732
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2723
              else
                2722
            else
              if p.val.testBit 0 then
                2721
              else
                2720
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2399
              else
                2398
            else
              if p.val.testBit 0 then
                2397
              else
                2396
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2387
              else
                2386
            else
              if p.val.testBit 0 then
                2385
              else
                2384
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2063
              else
                2062
            else
              if p.val.testBit 0 then
                2061
              else
                2060
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2051
              else
                2050
            else
              if p.val.testBit 0 then
                2049
              else
                2048
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2047
              else
                2046
            else
              if p.val.testBit 0 then
                2045
              else
                2044
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                2035
              else
                2034
            else
              if p.val.testBit 0 then
                2033
              else
                2032
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1711
              else
                1710
            else
              if p.val.testBit 0 then
                1709
              else
                1708
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1699
              else
                1698
            else
              if p.val.testBit 0 then
                1697
              else
                1696
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1375
              else
                1374
            else
              if p.val.testBit 0 then
                1373
              else
                1372
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1363
              else
                1362
            else
              if p.val.testBit 0 then
                1361
              else
                1360
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1039
              else
                1038
            else
              if p.val.testBit 0 then
                1037
              else
                1036
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1027
              else
                1026
            else
              if p.val.testBit 0 then
                1025
              else
                1024
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1023
              else
                1022
            else
              if p.val.testBit 0 then
                1021
              else
                1020
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1011
              else
                1010
            else
              if p.val.testBit 0 then
                1009
              else
                1008
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                687
              else
                686
            else
              if p.val.testBit 0 then
                685
              else
                684
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                675
              else
                674
            else
              if p.val.testBit 0 then
                673
              else
                672
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                351
              else
                350
            else
              if p.val.testBit 0 then
                349
              else
                348
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                339
              else
                338
            else
              if p.val.testBit 0 then
                337
              else
                336
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                15
              else
                14
            else
              if p.val.testBit 0 then
                13
              else
                12
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                3
              else
                2
            else
              if p.val.testBit 0 then
                1
              else
                0

/-- An explicit seven-coordinate inverse lookup for the output catalogue. -/
def monsterNortonLine01CompactOutputLookup (n : Fin 4096) : Fin 128 :=
  ⟨(((if n.val.testBit 0 then 1 else 0) +
      (if n.val.testBit 1 then 2 else 0) +
      (if n.val.testBit 3 then 4 else 0) +
      (if n.val.testBit 8 then 8 else 0) +
      (if n.val.testBit 9 then 16 else 0) +
      (if n.val.testBit 10 then 32 else 0) +
      (if n.val.testBit 11 then 64 else 0)) % 128), Nat.mod_lt _ (by norm_num)⟩

/-- The exact membership test for the specified output support catalogue. -/
def monsterNortonLine01CompactOutputSupport (n : Fin 4096) : Prop :=
  monsterNortonLine01CompactOutputLabel (monsterNortonLine01CompactOutputLookup n) = n

/-- The catalogue support is decided by finite index equality. -/
instance : DecidablePred monsterNortonLine01CompactOutputSupport := fun n =>
  inferInstanceAs (Decidable
    (monsterNortonLine01CompactOutputLabel (monsterNortonLine01CompactOutputLookup n) = n))

set_option maxRecDepth 10000 in
/-- Every catalogue coordinate is recovered by its explicit inverse lookup. -/
theorem monsterNortonLine01CompactOutputLookup_label (p : Fin 128) :
    monsterNortonLine01CompactOutputLookup (monsterNortonLine01CompactOutputLabel p) = p := by
  revert p
  decide +kernel

/-- Every displayed coordinate satisfies the exact support predicate. -/
theorem monsterNortonLine01CompactOutputLabel_support (p : Fin 128) :
    monsterNortonLine01CompactOutputSupport (monsterNortonLine01CompactOutputLabel p) := by
  unfold monsterNortonLine01CompactOutputSupport
  rw [monsterNortonLine01CompactOutputLookup_label]

/-- The proposed inverse integer numerator coefficients in the specified column order. -/
def monsterNortonLine01CompactOutputCoefficient (k : Fin 16) (p : Fin 128) : ℤ :=
  if k.val.testBit 3 then
    if k.val.testBit 2 then
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
    else
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
  else
    if k.val.testBit 2 then
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        32
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        32
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        (-32)
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
    else
      if k.val.testBit 1 then
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        32
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
      else
        if k.val.testBit 0 then
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
        else
          if p.val.testBit 6 then
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
          else
            if p.val.testBit 5 then
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        (-32)
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        32
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        0
                      else
                        0
                    else
                      if p.val.testBit 0 then
                        0
                      else
                        0
            else
              if p.val.testBit 4 then
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        (-8)
                      else
                        (-8)
                    else
                      if p.val.testBit 0 then
                        (-8)
                      else
                        8
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
              else
                if p.val.testBit 3 then
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                else
                  if p.val.testBit 2 then
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)
                  else
                    if p.val.testBit 1 then
                      if p.val.testBit 0 then
                        8
                      else
                        8
                    else
                      if p.val.testBit 0 then
                        8
                      else
                        (-8)

/-- The entire integer vector evaluated by the supported coefficient lookup. -/
def monsterNortonLine01CompactOutputVector (k : Fin 16) : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactOutputSupport n then
    monsterNortonLine01CompactOutputCoefficient k (monsterNortonLine01CompactOutputLookup n)
  else 0

/-- The coefficient lookup equals its explicit sparse sum as an entire integer vector. -/
theorem monsterNortonLine01CompactOutputVector_sparse (k : Fin 16) :
    monsterNortonLine01CompactOutputVector k =
      ∑ p : Fin 128, monsterNortonLine01CompactOutputCoefficient k p •
        (Pi.single (monsterNortonLine01CompactOutputLabel p) 1 : NortonUIntegerVector) := by
  exact (monsterNortonSparseLookup_eq monsterNortonLine01CompactOutputLabel
    monsterNortonLine01CompactOutputLookup monsterNortonLine01CompactOutputSupport
    monsterNortonLine01CompactOutputLookup_label monsterNortonLine01CompactOutputLabel_support
    (fun n hn => hn) (monsterNortonLine01CompactOutputCoefficient k)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
