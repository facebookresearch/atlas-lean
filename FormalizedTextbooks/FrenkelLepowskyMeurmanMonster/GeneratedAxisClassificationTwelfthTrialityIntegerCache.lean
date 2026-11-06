/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Every original integer octad Fourier sign is checked once against the actual source matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- One complete original Fourier row as its sixty-four signed bits. -/
def generatedTwelfthTrialityIntegerRows (i : Fin 64) : ℕ :=
  if i.val < 32 then
    if i.val < 16 then
      if i.val < 8 then
        if i.val < 4 then
          if i.val < 2 then
            if i.val < 1 then
              0x0
            else
              0x3cc3c33cc33c3cc3
          else
            if i.val < 3 then
              0x5aa5a55aa55a5aa5
            else
              0x9999999999999999
        else
          if i.val < 6 then
            if i.val < 5 then
              0x6699996699666699
            else
              0xa5a5a5a5a5a5a5a5
          else
            if i.val < 7 then
              0xc3c3c3c3c3c3c3c3
            else
              0xff0000ff00ffff00
      else
        if i.val < 12 then
          if i.val < 10 then
            if i.val < 9 then
              0x6969969696966969
            else
              0xaa55aa55aa55aa55
          else
            if i.val < 11 then
              0xcc33cc33cc33cc33
            else
              0xf0f00f0f0f0ff0f0
        else
          if i.val < 14 then
            if i.val < 13 then
              0xf00ff00ff00ff00f
            else
              0xcccc33333333cccc
          else
            if i.val < 15 then
              0xaaaa55555555aaaa
            else
              0x6996699669966996
    else
      if i.val < 24 then
        if i.val < 20 then
          if i.val < 18 then
            if i.val < 17 then
              0x6996699696699669
            else
              0xaaaa5555aaaa5555
          else
            if i.val < 19 then
              0xcccc3333cccc3333
            else
              0xf00ff00f0ff00ff0
        else
          if i.val < 22 then
            if i.val < 21 then
              0xf0f00f0ff0f00f0f
            else
              0xcc33cc3333cc33cc
          else
            if i.val < 23 then
              0xaa55aa5555aa55aa
            else
              0x6969969669699696
      else
        if i.val < 28 then
          if i.val < 26 then
            if i.val < 25 then
              0xff0000ffff0000ff
            else
              0xc3c3c3c33c3c3c3c
          else
            if i.val < 27 then
              0xa5a5a5a55a5a5a5a
            else
              0x6699996666999966
        else
          if i.val < 30 then
            if i.val < 29 then
              0x9999999966666666
            else
              0x5aa5a55a5aa5a55a
          else
            if i.val < 31 then
              0x3cc3c33c3cc3c33c
            else
              0xffffffff
  else
    if i.val < 48 then
      if i.val < 40 then
        if i.val < 36 then
          if i.val < 34 then
            if i.val < 33 then
              0x6996966969969669
            else
              0xaaaaaaaa55555555
          else
            if i.val < 35 then
              0xcccccccc33333333
            else
              0xf00f0ff0f00f0ff0
        else
          if i.val < 38 then
            if i.val < 37 then
              0xf0f0f0f00f0f0f0f
            else
              0xcc3333cccc3333cc
          else
            if i.val < 39 then
              0xaa5555aaaa5555aa
            else
              0x6969696996969696
      else
        if i.val < 44 then
          if i.val < 42 then
            if i.val < 41 then
              0xff00ff0000ff00ff
            else
              0xc3c33c3cc3c33c3c
          else
            if i.val < 43 then
              0xa5a55a5aa5a55a5a
            else
              0x6699669999669966
        else
          if i.val < 46 then
            if i.val < 45 then
              0x9999666699996666
            else
              0x5aa55aa5a55aa55a
          else
            if i.val < 47 then
              0x3cc33cc3c33cc33c
            else
              0xffff0000ffff
    else
      if i.val < 56 then
        if i.val < 52 then
          if i.val < 50 then
            if i.val < 49 then
              0xffff00000000ffff
            else
              0xc33cc33cc33cc33c
          else
            if i.val < 51 then
              0xa55aa55aa55aa55a
            else
              0x6666999999996666
        else
          if i.val < 54 then
            if i.val < 53 then
              0x9966996699669966
            else
              0x5a5aa5a5a5a55a5a
          else
            if i.val < 55 then
              0x3c3cc3c3c3c33c3c
            else
              0xff00ff00ff00ff
      else
        if i.val < 60 then
          if i.val < 58 then
            if i.val < 57 then
              0x9696969696969696
            else
              0x55aaaa55aa5555aa
          else
            if i.val < 59 then
              0x33cccc33cc3333cc
            else
              0xf0f0f0f0f0f0f0f
        else
          if i.val < 62 then
            if i.val < 61 then
              0xff0f00ff00f0ff0
            else
              0x3333333333333333
          else
            if i.val < 63 then
              0x5555555555555555
            else
              0x9669699669969669

/-- The complete exact original integer Fourier coefficient, including its quadratic diagonal. -/
def generatedTwelfthTrialityIntegerCache (i j : Fin 64) : ℤ :=
  if (generatedTwelfthTrialityIntegerRows i).testBit j.val then -1 else 1

set_option maxHeartbeats 8000000 in
-- Verify every original row and column sign directly in the kernel.
private theorem complete_certificate : ∀ i j : Fin 64,
    generatedTwelfthTrialityIntegerCache i j = trialityIntegerMatrix i j := by
  decide +kernel

/-- All four thousand ninety-six coefficients are the genuine original Fourier matrix entries. -/
theorem generatedTwelfth_triality_integer_cache_actual (i j : Fin 64) :
    generatedTwelfthTrialityIntegerCache i j = trialityIntegerMatrix i j :=
  complete_certificate i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
