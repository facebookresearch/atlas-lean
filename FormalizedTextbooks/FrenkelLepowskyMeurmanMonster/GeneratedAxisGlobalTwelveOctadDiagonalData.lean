/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortNumbers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! Candidate finite data of the octad-diagonal transition: the 120 nonzero preferred short
coordinates of the listed Octad representative, their images and phases under the two source
letters, the 120 nonzero short coordinates of the triality image, the intermediate matrix, and an
explicit frame. These are proposed data only; every use is kernel checked in later modules. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Source labels: the nonzero preferred short coordinates of the listed Octad representative. -/
def generatedAxisGlobalTwelveOctadDiagonalVLabel : Fin 120 → GriessShortIndex :=
  ![Sum.inl (0, 156), Sum.inl (0, 157), Sum.inl (0, 158), Sum.inl (0, 159), Sum.inl (0, 160),
    Sum.inl (0, 161), Sum.inl (0, 162), Sum.inl (0, 171), Sum.inl (0, 172), Sum.inl (0, 173),
    Sum.inl (0, 174), Sum.inl (0, 175), Sum.inl (0, 176), Sum.inl (0, 185), Sum.inl (0, 186),
    Sum.inl (0, 187), Sum.inl (0, 188), Sum.inl (0, 189), Sum.inl (0, 198), Sum.inl (0, 199),
    Sum.inl (0, 200), Sum.inl (0, 201), Sum.inl (0, 210), Sum.inl (0, 211), Sum.inl (0, 212),
    Sum.inl (0, 221), Sum.inl (0, 222), Sum.inl (0, 231), Sum.inl (1, 156), Sum.inl (1, 157),
    Sum.inl (1, 158), Sum.inl (1, 159), Sum.inl (1, 160), Sum.inl (1, 161), Sum.inl (1, 162),
    Sum.inl (1, 171), Sum.inl (1, 172), Sum.inl (1, 173), Sum.inl (1, 174), Sum.inl (1, 175),
    Sum.inl (1, 176), Sum.inl (1, 185), Sum.inl (1, 186), Sum.inl (1, 187), Sum.inl (1, 188),
    Sum.inl (1, 189), Sum.inl (1, 198), Sum.inl (1, 199), Sum.inl (1, 200), Sum.inl (1, 201),
    Sum.inl (1, 210), Sum.inl (1, 211), Sum.inl (1, 212), Sum.inl (1, 221), Sum.inl (1, 222),
    Sum.inl (1, 231), Sum.inr (Sum.inl (0, 0)), Sum.inr (Sum.inl (0, 1)),
    Sum.inr (Sum.inl (0, 2)), Sum.inr (Sum.inl (0, 3)), Sum.inr (Sum.inl (0, 4)),
    Sum.inr (Sum.inl (0, 5)), Sum.inr (Sum.inl (0, 6)), Sum.inr (Sum.inl (0, 7)),
    Sum.inr (Sum.inl (0, 8)), Sum.inr (Sum.inl (0, 9)), Sum.inr (Sum.inl (0, 10)),
    Sum.inr (Sum.inl (0, 11)), Sum.inr (Sum.inl (0, 12)), Sum.inr (Sum.inl (0, 13)),
    Sum.inr (Sum.inl (0, 14)), Sum.inr (Sum.inl (0, 15)), Sum.inr (Sum.inl (0, 16)),
    Sum.inr (Sum.inl (0, 17)), Sum.inr (Sum.inl (0, 18)), Sum.inr (Sum.inl (0, 19)),
    Sum.inr (Sum.inl (0, 20)), Sum.inr (Sum.inl (0, 21)), Sum.inr (Sum.inl (0, 22)),
    Sum.inr (Sum.inl (0, 23)), Sum.inr (Sum.inl (0, 24)), Sum.inr (Sum.inl (0, 25)),
    Sum.inr (Sum.inl (0, 26)), Sum.inr (Sum.inl (0, 27)), Sum.inr (Sum.inl (0, 28)),
    Sum.inr (Sum.inl (0, 29)), Sum.inr (Sum.inl (0, 30)), Sum.inr (Sum.inl (0, 31)),
    Sum.inr (Sum.inl (0, 32)), Sum.inr (Sum.inl (0, 33)), Sum.inr (Sum.inl (0, 34)),
    Sum.inr (Sum.inl (0, 35)), Sum.inr (Sum.inl (0, 36)), Sum.inr (Sum.inl (0, 37)),
    Sum.inr (Sum.inl (0, 38)), Sum.inr (Sum.inl (0, 39)), Sum.inr (Sum.inl (0, 40)),
    Sum.inr (Sum.inl (0, 41)), Sum.inr (Sum.inl (0, 42)), Sum.inr (Sum.inl (0, 43)),
    Sum.inr (Sum.inl (0, 44)), Sum.inr (Sum.inl (0, 45)), Sum.inr (Sum.inl (0, 46)),
    Sum.inr (Sum.inl (0, 47)), Sum.inr (Sum.inl (0, 48)), Sum.inr (Sum.inl (0, 49)),
    Sum.inr (Sum.inl (0, 50)), Sum.inr (Sum.inl (0, 51)), Sum.inr (Sum.inl (0, 52)),
    Sum.inr (Sum.inl (0, 53)), Sum.inr (Sum.inl (0, 54)), Sum.inr (Sum.inl (0, 55)),
    Sum.inr (Sum.inl (0, 56)), Sum.inr (Sum.inl (0, 57)), Sum.inr (Sum.inl (0, 58)),
    Sum.inr (Sum.inl (0, 59)), Sum.inr (Sum.inl (0, 60)), Sum.inr (Sum.inl (0, 61)),
    Sum.inr (Sum.inl (0, 62)), Sum.inr (Sum.inl (0, 63))]

/-- Their proposed coefficients. -/
def generatedAxisGlobalTwelveOctadDiagonalVCoeff : Fin 120 → ℚ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1,
    -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1]

/-- Proposed image labels under the two source letters. -/
def generatedAxisGlobalTwelveOctadDiagonalULabel : Fin 120 → GriessShortIndex :=
  ![Sum.inr (Sum.inl (510, 11)), Sum.inr (Sum.inl (506, 11)), Sum.inr (Sum.inl (507, 11)),
    Sum.inl (0, 45), Sum.inr (Sum.inl (510, 52)), Sum.inr (Sum.inl (506, 52)),
    Sum.inr (Sum.inl (507, 52)), Sum.inr (Sum.inl (9, 11)), Sum.inr (Sum.inl (8, 11)),
    Sum.inr (Sum.inl (510, 7)), Sum.inl (0, 123), Sum.inr (Sum.inl (9, 52)),
    Sum.inr (Sum.inl (8, 52)), Sum.inr (Sum.inl (0, 11)), Sum.inr (Sum.inl (506, 7)),
    Sum.inr (Sum.inl (9, 7)), Sum.inl (0, 185), Sum.inr (Sum.inl (0, 52)),
    Sum.inr (Sum.inl (507, 7)), Sum.inr (Sum.inl (8, 7)), Sum.inr (Sum.inl (0, 7)),
    Sum.inl (0, 231), Sum.inr (Sum.inl (510, 56)), Sum.inr (Sum.inl (506, 56)),
    Sum.inr (Sum.inl (507, 56)), Sum.inr (Sum.inl (9, 56)), Sum.inr (Sum.inl (8, 56)),
    Sum.inr (Sum.inl (0, 56)), Sum.inr (Sum.inl (510, 4)), Sum.inr (Sum.inl (506, 4)),
    Sum.inr (Sum.inl (507, 4)), Sum.inl (1, 0), Sum.inr (Sum.inl (510, 59)),
    Sum.inr (Sum.inl (506, 59)), Sum.inr (Sum.inl (507, 59)), Sum.inr (Sum.inl (9, 4)),
    Sum.inr (Sum.inl (8, 4)), Sum.inr (Sum.inl (510, 8)), Sum.inl (1, 86),
    Sum.inr (Sum.inl (9, 59)), Sum.inr (Sum.inl (8, 59)), Sum.inr (Sum.inl (0, 4)),
    Sum.inr (Sum.inl (506, 8)), Sum.inr (Sum.inl (9, 8)), Sum.inl (1, 156),
    Sum.inr (Sum.inl (0, 59)), Sum.inr (Sum.inl (507, 8)), Sum.inr (Sum.inl (8, 8)),
    Sum.inr (Sum.inl (0, 8)), Sum.inl (1, 210), Sum.inr (Sum.inl (510, 55)),
    Sum.inr (Sum.inl (506, 55)), Sum.inr (Sum.inl (507, 55)), Sum.inr (Sum.inl (9, 55)),
    Sum.inr (Sum.inl (8, 55)), Sum.inr (Sum.inl (0, 55)), Sum.inr (Sum.inl (533, 0)),
    Sum.inr (Sum.inl (152, 18)), Sum.inr (Sum.inl (532, 24)), Sum.inr (Sum.inl (151, 10)),
    Sum.inr (Sum.inl (533, 48)), Sum.inr (Sum.inl (152, 34)), Sum.inr (Sum.inl (532, 40)),
    Sum.inr (Sum.inl (151, 58)), Sum.inr (Sum.inl (534, 47)), Sum.inr (Sum.inl (153, 61)),
    Sum.inr (Sum.inl (531, 55)), Sum.inr (Sum.inl (150, 37)), Sum.inr (Sum.inl (534, 31)),
    Sum.inr (Sum.inl (153, 13)), Sum.inr (Sum.inl (531, 7)), Sum.inr (Sum.inl (150, 21)),
    Sum.inr (Sum.inl (152, 17)), Sum.inr (Sum.inl (533, 3)), Sum.inr (Sum.inl (151, 9)),
    Sum.inr (Sum.inl (532, 27)), Sum.inr (Sum.inl (152, 33)), Sum.inr (Sum.inl (533, 51)),
    Sum.inr (Sum.inl (151, 57)), Sum.inr (Sum.inl (532, 43)), Sum.inr (Sum.inl (153, 62)),
    Sum.inr (Sum.inl (534, 44)), Sum.inr (Sum.inl (150, 38)), Sum.inr (Sum.inl (531, 52)),
    Sum.inr (Sum.inl (153, 14)), Sum.inr (Sum.inl (534, 28)), Sum.inr (Sum.inl (150, 22)),
    Sum.inr (Sum.inl (531, 4)), Sum.inr (Sum.inl (532, 20)), Sum.inr (Sum.inl (151, 6)),
    Sum.inr (Sum.inl (533, 12)), Sum.inr (Sum.inl (152, 30)), Sum.inr (Sum.inl (532, 36)),
    Sum.inr (Sum.inl (151, 54)), Sum.inr (Sum.inl (533, 60)), Sum.inr (Sum.inl (152, 46)),
    Sum.inr (Sum.inl (531, 59)), Sum.inr (Sum.inl (150, 41)), Sum.inr (Sum.inl (534, 35)),
    Sum.inr (Sum.inl (153, 49)), Sum.inr (Sum.inl (531, 11)), Sum.inr (Sum.inl (150, 25)),
    Sum.inr (Sum.inl (534, 19)), Sum.inr (Sum.inl (153, 1)), Sum.inr (Sum.inl (151, 5)),
    Sum.inr (Sum.inl (532, 23)), Sum.inr (Sum.inl (152, 29)), Sum.inr (Sum.inl (533, 15)),
    Sum.inr (Sum.inl (151, 53)), Sum.inr (Sum.inl (532, 39)), Sum.inr (Sum.inl (152, 45)),
    Sum.inr (Sum.inl (533, 63)), Sum.inr (Sum.inl (150, 42)), Sum.inr (Sum.inl (531, 56)),
    Sum.inr (Sum.inl (153, 50)), Sum.inr (Sum.inl (534, 32)), Sum.inr (Sum.inl (150, 26)),
    Sum.inr (Sum.inl (531, 8)), Sum.inr (Sum.inl (153, 2)), Sum.inr (Sum.inl (534, 16))]

/-- Proposed central phases of the images. -/
def generatedAxisGlobalTwelveOctadDiagonalUPhase : Fin 120 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1,
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1]

/-- Proposed transported coefficients. -/
def generatedAxisGlobalTwelveOctadDiagonalUCoeff (k : Fin 120) : ℚ :=
  generatedAxisGlobalTwelveOctadDiagonalVCoeff k * (generatedAxisGlobalIntSign (generatedAxisGlobalTwelveOctadDiagonalUPhase k) : ℚ)

/-- Sparse lookup of the transported labels by their exact catalogue numbers. -/
def generatedAxisGlobalTwelveOctadDiagonalUTree : GeneratedAxisGlobalSparseLookupTree (Fin 120) :=
  (.branch 10393 99
    (.branch 1184 25
      (.branch 611 45
        (.branch 486 49
          (.branch 231 21
            (.branch 123 10
              (.branch 45 3
                .empty
                .empty)
              (.branch 185 16
                .empty
                .empty))
            (.branch 362 38
              (.branch 276 31
                .empty
                .empty)
              (.branch 432 44
                .empty
                .empty)))
          (.branch 563 13
            (.branch 559 20
              (.branch 556 41
                .empty
                .empty)
              (.branch 560 48
                .empty
                .empty))
            (.branch 607 55
              (.branch 604 17
                .empty
                .empty)
              (.branch 608 27
                .empty
                .empty))))
        (.branch 1123 40
          (.branch 1075 8
            (.branch 1071 19
              (.branch 1068 36
                .empty
                .empty)
              (.branch 1072 47
                .empty
                .empty))
            (.branch 1119 54
              (.branch 1116 12
                .empty
                .empty)
              (.branch 1120 26
                .empty
                .empty)))
          (.branch 1139 7
            (.branch 1135 15
              (.branch 1132 35
                .empty
                .empty)
              (.branch 1136 43
                .empty
                .empty))
            (.branch 1183 53
              (.branch 1180 11
                .empty
                .empty)
              .empty))))
      (.branch 10270 93
        (.branch 10193 97
          (.branch 10177 101
            (.branch 10173 71
              (.branch 1187 39
                .empty
                .empty)
              (.branch 10174 86
                .empty
                .empty))
            (.branch 10189 67
              (.branch 10178 116
                .empty
                .empty)
              (.branch 10190 82
                .empty
                .empty)))
          (.branch 10225 74
            (.branch 10221 104
              (.branch 10194 112
                .empty
                .empty)
              (.branch 10222 89
                .empty
                .empty))
            (.branch 10269 108
              (.branch 10226 59
                .empty
                .empty)
              .empty)))
        (.branch 10314 61
          (.branch 10298 57
            (.branch 10274 63
              (.branch 10273 78
                .empty
                .empty)
              (.branch 10297 72
                .empty
                .empty))
            (.branch 10310 91
              (.branch 10309 106
                .empty
                .empty)
              (.branch 10313 76
                .empty
                .empty)))
          (.branch 10346 118
            (.branch 10326 95
              (.branch 10325 110
                .empty
                .empty)
              (.branch 10345 103
                .empty
                .empty))
            (.branch 10358 84
              (.branch 10357 69
                .empty
                .empty)
              .empty)))))
    (.branch 34544 117
      (.branch 33011 2
        (.branch 32988 5
          (.branch 32940 29
            (.branch 10405 65
              (.branch 10394 114
                .empty
                .empty)
              (.branch 10406 80
                .empty
                .empty))
            (.branch 32944 42
              (.branch 32943 14
                .empty
                .empty)
              (.branch 32947 1
                .empty
                .empty)))
          (.branch 33004 30
            (.branch 32992 23
              (.branch 32991 51
                .empty
                .empty)
              (.branch 32995 33
                .empty
                .empty))
            (.branch 33008 46
              (.branch 33007 18
                .empty
                .empty)
              .empty)))
        (.branch 33203 0
          (.branch 33059 34
            (.branch 33055 52
              (.branch 33052 6
                .empty
                .empty)
              (.branch 33056 24
                .empty
                .empty))
            (.branch 33199 9
              (.branch 33196 28
                .empty
                .empty)
              (.branch 33200 37
                .empty
                .empty)))
          (.branch 33251 32
            (.branch 33247 50
              (.branch 33244 4
                .empty
                .empty)
              (.branch 33248 22
                .empty
                .empty))
            (.branch 34543 70
              (.branch 34540 87
                .empty
                .empty)
              .empty))))
      (.branch 34667 73
        (.branch 34624 58
          (.branch 34592 113
            (.branch 34588 83
              (.branch 34547 100
                .empty
                .empty)
              (.branch 34591 66
                .empty
                .empty))
            (.branch 34620 88
              (.branch 34595 96
                .empty
                .empty)
              (.branch 34623 105
                .empty
                .empty)))
          (.branch 34640 62
            (.branch 34636 92
              (.branch 34627 75
                .empty
                .empty)
              (.branch 34639 109
                .empty
                .empty))
            (.branch 34664 56
              (.branch 34643 79
                .empty
                .empty)
              .empty)))
        (.branch 34747 102
          (.branch 34715 77
            (.branch 34679 107
              (.branch 34676 90
                .empty
                .empty)
              (.branch 34712 60
                .empty
                .empty))
            (.branch 34727 111
              (.branch 34724 94
                .empty
                .empty)
              (.branch 34744 119
                .empty
                .empty)))
          (.branch 34763 98
            (.branch 34759 68
              (.branch 34756 85
                .empty
                .empty)
              (.branch 34760 115
                .empty
                .empty))
            (.branch 34775 64
              (.branch 34772 81
                .empty
                .empty)
              .empty))))))

/-- The transported label stored at a preferred short coordinate, if any. -/
def generatedAxisGlobalTwelveOctadDiagonalUSource (r : GriessShortIndex) : Option (Fin 120) :=
  generatedAxisGlobalSparseLookup generatedAxisGlobalTwelveOctadDiagonalUTree (generatedAxisGlobalShortNumber r)

/-- The candidate transported short coefficient. -/
def generatedAxisGlobalTwelveOctadDiagonalUShortQ (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalTwelveOctadDiagonalUSource r with
  | some k => generatedAxisGlobalTwelveOctadDiagonalUCoeff k
  | none => 0

/-- The proposed intermediate matrix coordinates. -/
def generatedAxisGlobalTwelveOctadDiagonalUMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  ![![1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The candidate intermediate rational packet. -/
def generatedAxisGlobalTwelveOctadDiagonalUPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalTwelveOctadDiagonalUMatrixQ, (generatedAxisGlobalTwelveOctadDiagonalUShortQ, 0))

/-- Labels of the 120 nonzero short coordinates of the triality image. -/
def generatedAxisGlobalTwelveOctadDiagonalXLabel : Fin 120 → GriessShortIndex :=
  ![Sum.inl (1, 0), Sum.inl (1, 45), Sum.inl (1, 86), Sum.inl (1, 123), Sum.inl (1, 156),
    Sum.inl (1, 185), Sum.inl (1, 210), Sum.inl (1, 231), Sum.inr (Sum.inl (0, 0)),
    Sum.inr (Sum.inl (0, 3)), Sum.inr (Sum.inl (0, 12)), Sum.inr (Sum.inl (0, 15)),
    Sum.inr (Sum.inl (0, 48)), Sum.inr (Sum.inl (0, 51)), Sum.inr (Sum.inl (0, 60)),
    Sum.inr (Sum.inl (0, 63)), Sum.inr (Sum.inl (8, 0)), Sum.inr (Sum.inl (8, 3)),
    Sum.inr (Sum.inl (8, 12)), Sum.inr (Sum.inl (8, 15)), Sum.inr (Sum.inl (8, 48)),
    Sum.inr (Sum.inl (8, 51)), Sum.inr (Sum.inl (8, 60)), Sum.inr (Sum.inl (8, 63)),
    Sum.inr (Sum.inl (9, 0)), Sum.inr (Sum.inl (9, 3)), Sum.inr (Sum.inl (9, 12)),
    Sum.inr (Sum.inl (9, 15)), Sum.inr (Sum.inl (9, 48)), Sum.inr (Sum.inl (9, 51)),
    Sum.inr (Sum.inl (9, 60)), Sum.inr (Sum.inl (9, 63)), Sum.inr (Sum.inl (150, 0)),
    Sum.inr (Sum.inl (150, 3)), Sum.inr (Sum.inl (150, 12)), Sum.inr (Sum.inl (150, 15)),
    Sum.inr (Sum.inl (150, 48)), Sum.inr (Sum.inl (150, 51)), Sum.inr (Sum.inl (150, 60)),
    Sum.inr (Sum.inl (150, 63)), Sum.inr (Sum.inl (151, 0)), Sum.inr (Sum.inl (151, 3)),
    Sum.inr (Sum.inl (151, 12)), Sum.inr (Sum.inl (151, 15)), Sum.inr (Sum.inl (151, 48)),
    Sum.inr (Sum.inl (151, 51)), Sum.inr (Sum.inl (151, 60)), Sum.inr (Sum.inl (151, 63)),
    Sum.inr (Sum.inl (152, 0)), Sum.inr (Sum.inl (152, 3)), Sum.inr (Sum.inl (152, 12)),
    Sum.inr (Sum.inl (152, 15)), Sum.inr (Sum.inl (152, 48)), Sum.inr (Sum.inl (152, 51)),
    Sum.inr (Sum.inl (152, 60)), Sum.inr (Sum.inl (152, 63)), Sum.inr (Sum.inl (153, 0)),
    Sum.inr (Sum.inl (153, 3)), Sum.inr (Sum.inl (153, 12)), Sum.inr (Sum.inl (153, 15)),
    Sum.inr (Sum.inl (153, 48)), Sum.inr (Sum.inl (153, 51)), Sum.inr (Sum.inl (153, 60)),
    Sum.inr (Sum.inl (153, 63)), Sum.inr (Sum.inl (506, 0)), Sum.inr (Sum.inl (506, 3)),
    Sum.inr (Sum.inl (506, 12)), Sum.inr (Sum.inl (506, 15)), Sum.inr (Sum.inl (506, 48)),
    Sum.inr (Sum.inl (506, 51)), Sum.inr (Sum.inl (506, 60)), Sum.inr (Sum.inl (506, 63)),
    Sum.inr (Sum.inl (507, 0)), Sum.inr (Sum.inl (507, 3)), Sum.inr (Sum.inl (507, 12)),
    Sum.inr (Sum.inl (507, 15)), Sum.inr (Sum.inl (507, 48)), Sum.inr (Sum.inl (507, 51)),
    Sum.inr (Sum.inl (507, 60)), Sum.inr (Sum.inl (507, 63)), Sum.inr (Sum.inl (510, 0)),
    Sum.inr (Sum.inl (510, 3)), Sum.inr (Sum.inl (510, 12)), Sum.inr (Sum.inl (510, 15)),
    Sum.inr (Sum.inl (510, 48)), Sum.inr (Sum.inl (510, 51)), Sum.inr (Sum.inl (510, 60)),
    Sum.inr (Sum.inl (510, 63)), Sum.inr (Sum.inl (531, 0)), Sum.inr (Sum.inl (531, 3)),
    Sum.inr (Sum.inl (531, 12)), Sum.inr (Sum.inl (531, 15)), Sum.inr (Sum.inl (531, 48)),
    Sum.inr (Sum.inl (531, 51)), Sum.inr (Sum.inl (531, 60)), Sum.inr (Sum.inl (531, 63)),
    Sum.inr (Sum.inl (532, 0)), Sum.inr (Sum.inl (532, 3)), Sum.inr (Sum.inl (532, 12)),
    Sum.inr (Sum.inl (532, 15)), Sum.inr (Sum.inl (532, 48)), Sum.inr (Sum.inl (532, 51)),
    Sum.inr (Sum.inl (532, 60)), Sum.inr (Sum.inl (532, 63)), Sum.inr (Sum.inl (533, 0)),
    Sum.inr (Sum.inl (533, 3)), Sum.inr (Sum.inl (533, 12)), Sum.inr (Sum.inl (533, 15)),
    Sum.inr (Sum.inl (533, 48)), Sum.inr (Sum.inl (533, 51)), Sum.inr (Sum.inl (533, 60)),
    Sum.inr (Sum.inl (533, 63)), Sum.inr (Sum.inl (534, 0)), Sum.inr (Sum.inl (534, 3)),
    Sum.inr (Sum.inl (534, 12)), Sum.inr (Sum.inl (534, 15)), Sum.inr (Sum.inl (534, 48)),
    Sum.inr (Sum.inl (534, 51)), Sum.inr (Sum.inl (534, 60)), Sum.inr (Sum.inl (534, 63))]

/-- Their proposed coefficients. -/
def generatedAxisGlobalTwelveOctadDiagonalXCoeff : Fin 120 → ℚ :=
  ![-1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1,
    1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1]

/-- Sparse lookup of the triality-image labels. -/
def generatedAxisGlobalTwelveOctadDiagonalXTree : GeneratedAxisGlobalSparseLookupTree (Fin 120) :=
  (.branch 10392 60
    (.branch 1188 30
      (.branch 615 15
        (.branch 507 7
          (.branch 399 3
            (.branch 321 1
              (.branch 276 0
                .empty
                .empty)
              (.branch 362 2
                .empty
                .empty))
            (.branch 461 5
              (.branch 432 4
                .empty
                .empty)
              (.branch 486 6
                .empty
                .empty)))
          (.branch 567 11
            (.branch 555 9
              (.branch 552 8
                .empty
                .empty)
              (.branch 564 10
                .empty
                .empty))
            (.branch 603 13
              (.branch 600 12
                .empty
                .empty)
              (.branch 612 14
                .empty
                .empty))))
        (.branch 1127 23
          (.branch 1079 19
            (.branch 1067 17
              (.branch 1064 16
                .empty
                .empty)
              (.branch 1076 18
                .empty
                .empty))
            (.branch 1115 21
              (.branch 1112 20
                .empty
                .empty)
              (.branch 1124 22
                .empty
                .empty)))
          (.branch 1143 27
            (.branch 1131 25
              (.branch 1128 24
                .empty
                .empty)
              (.branch 1140 26
                .empty
                .empty))
            (.branch 1179 29
              (.branch 1176 28
                .empty
                .empty)
              .empty))))
      (.branch 10267 45
        (.branch 10212 38
          (.branch 10164 34
            (.branch 10152 32
              (.branch 1191 31
                .empty
                .empty)
              (.branch 10155 33
                .empty
                .empty))
            (.branch 10200 36
              (.branch 10167 35
                .empty
                .empty)
              (.branch 10203 37
                .empty
                .empty)))
          (.branch 10228 42
            (.branch 10216 40
              (.branch 10215 39
                .empty
                .empty)
              (.branch 10219 41
                .empty
                .empty))
            (.branch 10264 44
              (.branch 10231 43
                .empty
                .empty)
              .empty)))
        (.branch 10331 53
          (.branch 10283 49
            (.branch 10279 47
              (.branch 10276 46
                .empty
                .empty)
              (.branch 10280 48
                .empty
                .empty))
            (.branch 10295 51
              (.branch 10292 50
                .empty
                .empty)
              (.branch 10328 52
                .empty
                .empty)))
          (.branch 10347 57
            (.branch 10343 55
              (.branch 10340 54
                .empty
                .empty)
              (.branch 10344 56
                .empty
                .empty))
            (.branch 10359 59
              (.branch 10356 58
                .empty
                .empty)
              .empty)))))
    (.branch 34548 90
      (.branch 33015 75
        (.branch 32984 68
          (.branch 32936 64
            (.branch 10404 62
              (.branch 10395 61
                .empty
                .empty)
              (.branch 10407 63
                .empty
                .empty))
            (.branch 32948 66
              (.branch 32939 65
                .empty
                .empty)
              (.branch 32951 67
                .empty
                .empty)))
          (.branch 33000 72
            (.branch 32996 70
              (.branch 32987 69
                .empty
                .empty)
              (.branch 32999 71
                .empty
                .empty))
            (.branch 33012 74
              (.branch 33003 73
                .empty
                .empty)
              .empty)))
        (.branch 33207 83
          (.branch 33063 79
            (.branch 33051 77
              (.branch 33048 76
                .empty
                .empty)
              (.branch 33060 78
                .empty
                .empty))
            (.branch 33195 81
              (.branch 33192 80
                .empty
                .empty)
              (.branch 33204 82
                .empty
                .empty)))
          (.branch 33255 87
            (.branch 33243 85
              (.branch 33240 84
                .empty
                .empty)
              (.branch 33252 86
                .empty
                .empty))
            (.branch 34539 89
              (.branch 34536 88
                .empty
                .empty)
              .empty))))
      (.branch 34667 105
        (.branch 34612 98
          (.branch 34596 94
            (.branch 34584 92
              (.branch 34551 91
                .empty
                .empty)
              (.branch 34587 93
                .empty
                .empty))
            (.branch 34600 96
              (.branch 34599 95
                .empty
                .empty)
              (.branch 34603 97
                .empty
                .empty)))
          (.branch 34660 102
            (.branch 34648 100
              (.branch 34615 99
                .empty
                .empty)
              (.branch 34651 101
                .empty
                .empty))
            (.branch 34664 104
              (.branch 34663 103
                .empty
                .empty)
              .empty)))
        (.branch 34731 113
          (.branch 34715 109
            (.branch 34679 107
              (.branch 34676 106
                .empty
                .empty)
              (.branch 34712 108
                .empty
                .empty))
            (.branch 34727 111
              (.branch 34724 110
                .empty
                .empty)
              (.branch 34728 112
                .empty
                .empty)))
          (.branch 34779 117
            (.branch 34743 115
              (.branch 34740 114
                .empty
                .empty)
              (.branch 34776 116
                .empty
                .empty))
            (.branch 34791 119
              (.branch 34788 118
                .empty
                .empty)
              .empty))))))

/-- The triality-image label stored at a preferred short coordinate, if any. -/
def generatedAxisGlobalTwelveOctadDiagonalXSource (r : GriessShortIndex) : Option (Fin 120) :=
  generatedAxisGlobalSparseLookup generatedAxisGlobalTwelveOctadDiagonalXTree (generatedAxisGlobalShortNumber r)

/-- The candidate triality-image short coefficient. -/
def generatedAxisGlobalTwelveOctadDiagonalXShortQ (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalTwelveOctadDiagonalXSource r with
  | some k => generatedAxisGlobalTwelveOctadDiagonalXCoeff k
  | none => 0

/-- The fourteen octads carrying nonzero octad coordinates. -/
def generatedAxisGlobalTwelveOctadDiagonalActiveOctad : Fin 14 → Fin 759 :=
  ![0, 8, 9, 150, 151, 152, 153, 506, 507, 510, 531, 532, 533, 534]

/-- Proposed standard-octad labels of the frame images of the triality-image support. -/
def generatedAxisGlobalTwelveOctadDiagonalXTarget : Fin 120 → GriessShortIndex :=
  ![Sum.inl (1, 159), Sum.inl (0, 159), Sum.inl (1, 174), Sum.inl (0, 174), Sum.inl (1, 188),
    Sum.inl (0, 188), Sum.inl (1, 201), Sum.inl (0, 201), Sum.inl (1, 185), Sum.inl (0, 200),
    Sum.inl (1, 200), Sum.inl (0, 185), Sum.inl (0, 189), Sum.inl (1, 231), Sum.inl (0, 231),
    Sum.inl (1, 189), Sum.inl (1, 172), Sum.inl (0, 199), Sum.inl (1, 199), Sum.inl (0, 172),
    Sum.inl (0, 176), Sum.inl (1, 222), Sum.inl (0, 222), Sum.inl (1, 176), Sum.inl (1, 171),
    Sum.inl (0, 187), Sum.inl (1, 187), Sum.inl (0, 171), Sum.inl (0, 175), Sum.inl (1, 221),
    Sum.inl (0, 221), Sum.inl (1, 175), Sum.inr (Sum.inl (0, 15)), Sum.inr (Sum.inl (0, 30)),
    Sum.inr (Sum.inl (0, 45)), Sum.inr (Sum.inl (0, 60)), Sum.inr (Sum.inl (0, 11)),
    Sum.inr (Sum.inl (0, 26)), Sum.inr (Sum.inl (0, 41)), Sum.inr (Sum.inl (0, 56)),
    Sum.inr (Sum.inl (0, 48)), Sum.inr (Sum.inl (0, 33)), Sum.inr (Sum.inl (0, 18)),
    Sum.inr (Sum.inl (0, 3)), Sum.inr (Sum.inl (0, 52)), Sum.inr (Sum.inl (0, 37)),
    Sum.inr (Sum.inl (0, 22)), Sum.inr (Sum.inl (0, 7)), Sum.inr (Sum.inl (0, 16)),
    Sum.inr (Sum.inl (0, 1)), Sum.inr (Sum.inl (0, 50)), Sum.inr (Sum.inl (0, 35)),
    Sum.inr (Sum.inl (0, 20)), Sum.inr (Sum.inl (0, 5)), Sum.inr (Sum.inl (0, 54)),
    Sum.inr (Sum.inl (0, 39)), Sum.inr (Sum.inl (0, 47)), Sum.inr (Sum.inl (0, 62)),
    Sum.inr (Sum.inl (0, 13)), Sum.inr (Sum.inl (0, 28)), Sum.inr (Sum.inl (0, 43)),
    Sum.inr (Sum.inl (0, 58)), Sum.inr (Sum.inl (0, 9)), Sum.inr (Sum.inl (0, 24)),
    Sum.inl (1, 157), Sum.inl (0, 186), Sum.inl (1, 186), Sum.inl (0, 157), Sum.inl (0, 161),
    Sum.inl (1, 211), Sum.inl (0, 211), Sum.inl (1, 161), Sum.inl (1, 158), Sum.inl (0, 198),
    Sum.inl (1, 198), Sum.inl (0, 158), Sum.inl (0, 162), Sum.inl (1, 212), Sum.inl (0, 212),
    Sum.inl (1, 162), Sum.inl (1, 156), Sum.inl (0, 173), Sum.inl (1, 173), Sum.inl (0, 156),
    Sum.inl (0, 160), Sum.inl (1, 210), Sum.inl (0, 210), Sum.inl (1, 160),
    Sum.inr (Sum.inl (0, 31)), Sum.inr (Sum.inl (0, 14)), Sum.inr (Sum.inl (0, 61)),
    Sum.inr (Sum.inl (0, 44)), Sum.inr (Sum.inl (0, 27)), Sum.inr (Sum.inl (0, 10)),
    Sum.inr (Sum.inl (0, 57)), Sum.inr (Sum.inl (0, 40)), Sum.inr (Sum.inl (0, 32)),
    Sum.inr (Sum.inl (0, 49)), Sum.inr (Sum.inl (0, 2)), Sum.inr (Sum.inl (0, 19)),
    Sum.inr (Sum.inl (0, 36)), Sum.inr (Sum.inl (0, 53)), Sum.inr (Sum.inl (0, 6)),
    Sum.inr (Sum.inl (0, 23)), Sum.inr (Sum.inl (0, 0)), Sum.inr (Sum.inl (0, 17)),
    Sum.inr (Sum.inl (0, 34)), Sum.inr (Sum.inl (0, 51)), Sum.inr (Sum.inl (0, 4)),
    Sum.inr (Sum.inl (0, 21)), Sum.inr (Sum.inl (0, 38)), Sum.inr (Sum.inl (0, 55)),
    Sum.inr (Sum.inl (0, 63)), Sum.inr (Sum.inl (0, 46)), Sum.inr (Sum.inl (0, 29)),
    Sum.inr (Sum.inl (0, 12)), Sum.inr (Sum.inl (0, 59)), Sum.inr (Sum.inl (0, 42)),
    Sum.inr (Sum.inl (0, 25)), Sum.inr (Sum.inl (0, 8))]

/-- Proposed physical signs of those frame images. -/
def generatedAxisGlobalTwelveOctadDiagonalXVectorSign : Fin 120 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1,
    1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1,
    1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- The proposed rational physical frame matrix. -/
def generatedAxisGlobalTwelveOctadDiagonalFrameQ : Matrix (Fin 24) (Fin 24) ℚ :=
  ![![-1 / 2, 1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1 / 2, 1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1 / 2, -1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1 / 2, 1 / 2, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1 / 2, 1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, -1 / 2, -1 / 2, -1 / 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 1 / 2, -1 / 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, -1 / 2, 1 / 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1 / 2, -1 / 2, -1 / 2, -1 / 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2, -1 / 2, -1 / 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, -1 / 2, 1 / 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 1 / 2, -1 / 2]]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
