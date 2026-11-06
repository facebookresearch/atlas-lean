/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceInitialTensorSparseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactQCertificatesAssembly

/-! Ungated 128 fixed full-Q candidate images from the genuine original source unit tables.
Every word packs 24 base bits and its original central bit at position24. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original low and upper source labels stay in their actual dictionary coordinates. -/
def generatedTenthSourceSparseFastLabel
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) : Fin 4096 :=
  if b = 0 then generatedTenthSourceInitialTensorSparseLow p else
    generatedTenthSourceInitialTensorSparseHigh p

/-- The complete fixed images retain translation, modulation, and central phase. -/
def generatedTenthSourceSparseFastQWord : Fin 2 → Fin 8 → Fin 8 → ℕ :=
  ![
    ![
      ![6495320, 24108200, 7828453, 7543991, 1702669, 6440029, 18115406, 6282270],
      ![22221912, 6280360, 21461989, 21173431, 5731260, 18662636, 23784447, 17913007],
      ![1051818, 18664538, 20212503, 19924037, 2438141, 22973613, 23837516, 18877468],
      ![18875562, 2933850, 287511, 3141, 2663358, 6493422, 22422287, 2989151],
      ![18717929, 2184217, 17429332, 4035590, 4596704, 7541761, 19926259, 20263698],
      ![22424505, 23782217, 7490564, 4598614, 3234880, 25154801, 3984387, 21122226],
      ![6693817, 5958473, 21120004, 24519510, 21685008, 20210593, 7830355, 3797986],
      ![2987241, 17914905, 3799892, 17669126, 4037808, 20489041, 8108963, 21924930]
    ],
    ![
      ![5302103, 22816679, 21268714, 21030840, 19529730, 5357394, 2592833, 7087889],
      ![23129943, 7090087, 7635178, 7401400, 6588595, 3096547, 22614256, 2273184],
      ![19134373, 3094357, 17272856, 17039178, 18270450, 23951266, 22560835, 1308435],
      ![1310629, 18825045, 3643416, 3405642, 18569393, 5304289, 23451648, 18769744],
      ![3041254, 18001686, 20580443, 945929, 24500463, 21032718, 17037308, 17221661],
      ![23449782, 22616134, 21083915, 24498265, 173903, 4993022, 997132, 7452605],
      ![5626038, 6885446, 7454475, 4577369, 7936031, 17275054, 21266524, 657645],
      ![18771942, 2270998, 655451, 20866825, 944063, 17520734, 21512364, 8222541]
    ]
  ]

/-- Decode each fixed candidate in the genuine Q extension, including its central coefficient. -/
def generatedTenthSourceSparseFastQ
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) : Q :=
  let word := generatedTenthSourceSparseFastQWord b p.1 p.2
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (n := 24) (word % 16777216)),
    ofAdd (if word.testBit 24 then (1 : ZMod 2) else 0)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
