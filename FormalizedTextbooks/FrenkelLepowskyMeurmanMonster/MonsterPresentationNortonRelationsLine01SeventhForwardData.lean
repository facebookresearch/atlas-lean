/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Proposed finite packets for the next actual Norton U spin action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01InverseSupported

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Signed integer data in the fixed genuine 128-label input catalogue. -/
def monsterNortonLine01SeventhForwardCoefficient (i : Fin 16) (p : Fin 128) : ℤ :=
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
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
      else
        if i.val < 3 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
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
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
      else
        if i.val < 7 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        -1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        -1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        1
                      else
                        0
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
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
      else
        if i.val < 11 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        -1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        -1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        -1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        -1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
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
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        -8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        -1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        -1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        -1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        -1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        -1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        -1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        -1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        -1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
      else
        if i.val < 15 then
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        -1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        -1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        -1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        -1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        -1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        -1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        -1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        -1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        -1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        -1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        -1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        -1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        -1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        -1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        -1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        -1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0
        else
          if p.val < 64 then
            if p.val < 32 then
              if p.val < 16 then
                if p.val < 8 then
                  if p.val < 4 then
                    if p.val < 2 then
                      if p.val < 1 then
                        0
                      else
                        1
                    else
                      if p.val < 3 then
                        0
                      else
                        1
                  else
                    if p.val < 6 then
                      if p.val < 5 then
                        8
                      else
                        1
                    else
                      if p.val < 7 then
                        0
                      else
                        1
                else
                  if p.val < 12 then
                    if p.val < 10 then
                      if p.val < 9 then
                        0
                      else
                        -1
                    else
                      if p.val < 11 then
                        0
                      else
                        -1
                  else
                    if p.val < 14 then
                      if p.val < 13 then
                        0
                      else
                        -1
                    else
                      if p.val < 15 then
                        0
                      else
                        -1
              else
                if p.val < 24 then
                  if p.val < 20 then
                    if p.val < 18 then
                      if p.val < 17 then
                        0
                      else
                        -1
                    else
                      if p.val < 19 then
                        0
                      else
                        -1
                  else
                    if p.val < 22 then
                      if p.val < 21 then
                        0
                      else
                        -1
                    else
                      if p.val < 23 then
                        0
                      else
                        -1
                else
                  if p.val < 28 then
                    if p.val < 26 then
                      if p.val < 25 then
                        0
                      else
                        1
                    else
                      if p.val < 27 then
                        0
                      else
                        1
                  else
                    if p.val < 30 then
                      if p.val < 29 then
                        0
                      else
                        1
                    else
                      if p.val < 31 then
                        0
                      else
                        1
            else
              if p.val < 48 then
                if p.val < 40 then
                  if p.val < 36 then
                    if p.val < 34 then
                      if p.val < 33 then
                        -1
                      else
                        0
                    else
                      if p.val < 35 then
                        -1
                      else
                        0
                  else
                    if p.val < 38 then
                      if p.val < 37 then
                        -1
                      else
                        0
                    else
                      if p.val < 39 then
                        -1
                      else
                        0
                else
                  if p.val < 44 then
                    if p.val < 42 then
                      if p.val < 41 then
                        1
                      else
                        0
                    else
                      if p.val < 43 then
                        1
                      else
                        0
                  else
                    if p.val < 46 then
                      if p.val < 45 then
                        1
                      else
                        0
                    else
                      if p.val < 47 then
                        1
                      else
                        0
              else
                if p.val < 56 then
                  if p.val < 52 then
                    if p.val < 50 then
                      if p.val < 49 then
                        1
                      else
                        0
                    else
                      if p.val < 51 then
                        1
                      else
                        0
                  else
                    if p.val < 54 then
                      if p.val < 53 then
                        1
                      else
                        0
                    else
                      if p.val < 55 then
                        1
                      else
                        0
                else
                  if p.val < 60 then
                    if p.val < 58 then
                      if p.val < 57 then
                        -1
                      else
                        0
                    else
                      if p.val < 59 then
                        -1
                      else
                        0
                  else
                    if p.val < 62 then
                      if p.val < 61 then
                        -1
                      else
                        0
                    else
                      if p.val < 63 then
                        -1
                      else
                        0
          else
            if p.val < 96 then
              if p.val < 80 then
                if p.val < 72 then
                  if p.val < 68 then
                    if p.val < 66 then
                      if p.val < 65 then
                        0
                      else
                        1
                    else
                      if p.val < 67 then
                        0
                      else
                        1
                  else
                    if p.val < 70 then
                      if p.val < 69 then
                        -8
                      else
                        1
                    else
                      if p.val < 71 then
                        0
                      else
                        1
                else
                  if p.val < 76 then
                    if p.val < 74 then
                      if p.val < 73 then
                        0
                      else
                        -1
                    else
                      if p.val < 75 then
                        0
                      else
                        -1
                  else
                    if p.val < 78 then
                      if p.val < 77 then
                        0
                      else
                        -1
                    else
                      if p.val < 79 then
                        0
                      else
                        -1
              else
                if p.val < 88 then
                  if p.val < 84 then
                    if p.val < 82 then
                      if p.val < 81 then
                        0
                      else
                        -1
                    else
                      if p.val < 83 then
                        0
                      else
                        -1
                  else
                    if p.val < 86 then
                      if p.val < 85 then
                        0
                      else
                        -1
                    else
                      if p.val < 87 then
                        0
                      else
                        -1
                else
                  if p.val < 92 then
                    if p.val < 90 then
                      if p.val < 89 then
                        0
                      else
                        1
                    else
                      if p.val < 91 then
                        0
                      else
                        1
                  else
                    if p.val < 94 then
                      if p.val < 93 then
                        0
                      else
                        1
                    else
                      if p.val < 95 then
                        0
                      else
                        1
            else
              if p.val < 112 then
                if p.val < 104 then
                  if p.val < 100 then
                    if p.val < 98 then
                      if p.val < 97 then
                        -1
                      else
                        0
                    else
                      if p.val < 99 then
                        -1
                      else
                        0
                  else
                    if p.val < 102 then
                      if p.val < 101 then
                        -1
                      else
                        0
                    else
                      if p.val < 103 then
                        -1
                      else
                        0
                else
                  if p.val < 108 then
                    if p.val < 106 then
                      if p.val < 105 then
                        1
                      else
                        0
                    else
                      if p.val < 107 then
                        1
                      else
                        0
                  else
                    if p.val < 110 then
                      if p.val < 109 then
                        1
                      else
                        0
                    else
                      if p.val < 111 then
                        1
                      else
                        0
              else
                if p.val < 120 then
                  if p.val < 116 then
                    if p.val < 114 then
                      if p.val < 113 then
                        1
                      else
                        0
                    else
                      if p.val < 115 then
                        1
                      else
                        0
                  else
                    if p.val < 118 then
                      if p.val < 117 then
                        1
                      else
                        0
                    else
                      if p.val < 119 then
                        1
                      else
                        0
                else
                  if p.val < 124 then
                    if p.val < 122 then
                      if p.val < 121 then
                        -1
                      else
                        0
                    else
                      if p.val < 123 then
                        -1
                      else
                        0
                  else
                    if p.val < 126 then
                      if p.val < 125 then
                        -1
                      else
                        0
                    else
                      if p.val < 127 then
                        -1
                      else
                        0

/-- A proposed spin packet, with explicit zero values outside the actual input catalogue. -/
def monsterNortonLine01SeventhForwardPacket (i : Fin 16) : NortonUIntegerVector :=
  fun n => if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01SeventhForwardCoefficient i (monsterNortonLine01CompactInputLookup n)
      else 0

/-- The actual inverse of the proposed packet vanishes outside the output catalogue. -/
theorem monsterNortonLine01SeventhForward_inverse_zero (i : Fin 16) (n : Fin 4096)
    (hn : ¬ monsterNortonLine01CompactOutputSupport n) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01SeventhForwardPacket i) n = 0 := by
  apply monsterNortonLine01CompactInverse_supported _ _ _ hn
  intro m hm
  exact ite_eq_right hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
