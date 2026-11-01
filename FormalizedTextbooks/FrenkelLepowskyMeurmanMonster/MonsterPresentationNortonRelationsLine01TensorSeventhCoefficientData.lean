/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Integer coefficient data for the original seventh first-line tensor coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OddSixthCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original 128 output labels after the genuine Norton v translation. -/
def monsterNortonLine01TensorSpinLabel (p : Fin 128) : Fin 4096 :=
  monsterNortonBitXor (monsterNortonLine01CompactOutputLabel p) 1038

/-- The integer table used for the sixteen physical rows and 128 spin coordinates. -/
def monsterNortonLine01TensorSeventhCoefficientLookup (i : Fin 16) (p : Fin 128) : ℤ :=
  if i.val < 8 then
    if i.val < 4 then
      if i.val < 2 then
        if i.val < 1 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-192)
                      else
                        64
                    else
                      if p.val < 3 then
                        64
                      else
                        64
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        320
                      else
                        64
                    else
                      if p.val < 7 then
                        64
                      else
                        64
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        64
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        64
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        64
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        64
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        64
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        64
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-320)
                      else
                        (-64)
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        192
                      else
                        (-64)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-320)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        192
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-192)
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        320
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
      else
        if i.val < 3 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-320)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        192
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-192)
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        320
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-320)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        192
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-192)
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        320
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
    else
      if i.val < 6 then
        if i.val < 5 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        64
                      else
                        64
                    else
                      if p.val < 3 then
                        64
                      else
                        (-192)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        64
                      else
                        64
                    else
                      if p.val < 7 then
                        64
                      else
                        320
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        64
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        64
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        64
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        64
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        64
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        64
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-320)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        192
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-320)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        192
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        (-192)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        320
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
      else
        if i.val < 7 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-320)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        192
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        (-192)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        320
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-320)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        192
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        (-192)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        320
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
  else
    if i.val < 12 then
      if i.val < 10 then
        if i.val < 9 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        64
                      else
                        320
                    else
                      if p.val < 3 then
                        64
                      else
                        64
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        64
                      else
                        (-192)
                    else
                      if p.val < 7 then
                        64
                      else
                        64
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        64
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        64
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        64
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        64
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        64
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        64
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-64)
                      else
                        192
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        (-64)
                      else
                        (-320)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        192
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-320)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        320
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        (-192)
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
      else
        if i.val < 11 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        192
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-320)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        320
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        (-192)
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        192
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-320)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        64
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        64
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        320
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        (-192)
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
    else
      if i.val < 14 then
        if i.val < 13 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 3 then
                        192
                      else
                        (-64)
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 7 then
                        (-320)
                      else
                        (-64)
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 11 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 15 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 19 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 23 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 27 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 31 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 35 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 39 then
                        (-64)
                      else
                        64
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 43 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 47 then
                        (-64)
                      else
                        64
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 51 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 55 then
                        (-64)
                      else
                        64
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 59 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 63 then
                        (-64)
                      else
                        64
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        64
                      else
                        64
                    else
                      if p.val < 67 then
                        320
                      else
                        64
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        64
                      else
                        64
                    else
                      if p.val < 71 then
                        (-192)
                      else
                        64
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        64
                      else
                        64
                    else
                      if p.val < 75 then
                        64
                      else
                        64
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        64
                      else
                        64
                    else
                      if p.val < 79 then
                        64
                      else
                        64
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        64
                      else
                        64
                    else
                      if p.val < 83 then
                        64
                      else
                        64
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        64
                      else
                        64
                    else
                      if p.val < 87 then
                        64
                      else
                        64
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        64
                      else
                        64
                    else
                      if p.val < 91 then
                        64
                      else
                        64
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        64
                      else
                        64
                    else
                      if p.val < 95 then
                        64
                      else
                        64
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 99 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 103 then
                        (-64)
                      else
                        64
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 107 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 111 then
                        (-64)
                      else
                        64
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 115 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 119 then
                        (-64)
                      else
                        64
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 123 then
                        64
                      else
                        (-64)
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 127 then
                        (-64)
                      else
                        64
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        64
                      else
                        64
                    else
                      if p.val < 3 then
                        64
                      else
                        64
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        64
                      else
                        64
                    else
                      if p.val < 7 then
                        64
                      else
                        64
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        320
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        (-192)
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        64
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        64
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        64
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        64
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        192
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-320)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)
      else
        if i.val < 15 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        64
                      else
                        64
                    else
                      if p.val < 3 then
                        64
                      else
                        64
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        64
                      else
                        64
                    else
                      if p.val < 7 then
                        64
                      else
                        64
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        64
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        64
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        320
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        (-192)
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        64
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        64
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        192
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-320)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-64)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        64
                      else
                        64
                    else
                      if p.val < 3 then
                        64
                      else
                        64
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        64
                      else
                        64
                    else
                      if p.val < 7 then
                        64
                      else
                        64
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        64
                      else
                        64
                    else
                      if p.val < 11 then
                        64
                      else
                        64
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        64
                      else
                        64
                    else
                      if p.val < 15 then
                        64
                      else
                        64
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        64
                      else
                        64
                    else
                      if p.val < 19 then
                        64
                      else
                        64
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        64
                      else
                        64
                    else
                      if p.val < 23 then
                        64
                      else
                        64
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        64
                      else
                        64
                    else
                      if p.val < 27 then
                        320
                      else
                        64
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        64
                      else
                        64
                    else
                      if p.val < 31 then
                        (-192)
                      else
                        64
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 35 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 39 then
                        64
                      else
                        (-64)
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 43 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 47 then
                        64
                      else
                        (-64)
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 51 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 55 then
                        64
                      else
                        (-64)
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 59 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 63 then
                        64
                      else
                        (-64)
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 67 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 71 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 75 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 79 then
                        (-64)
                      else
                        (-64)
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 83 then
                        (-64)
                      else
                        (-64)
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 87 then
                        (-64)
                      else
                        (-64)
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 91 then
                        192
                      else
                        (-64)
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        (-64)
                      else
                        (-64)
                    else
                      if p.val < 95 then
                        (-320)
                      else
                        (-64)
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 99 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 103 then
                        64
                      else
                        (-64)
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 107 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 111 then
                        64
                      else
                        (-64)
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 115 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 119 then
                        64
                      else
                        (-64)
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        64
                      else
                        (-64)
                    else
                      if p.val < 123 then
                        (-64)
                      else
                        64
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        (-64)
                      else
                        64
                    else
                      if p.val < 127 then
                        64
                      else
                        (-64)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
