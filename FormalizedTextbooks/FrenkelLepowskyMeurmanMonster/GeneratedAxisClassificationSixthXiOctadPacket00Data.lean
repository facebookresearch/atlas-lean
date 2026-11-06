/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQDecidable

/-! Original Xi octad-source packet with genuine cached output families and full phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Genuine output-family addresses, requiring original physical and coefficient certificates -/
def generatedSixthXiOctadPacket00OutputAddress : Fin 64 → Fin 231 × Fin 64 :=
  ![(226, 8), (67, 61), (226, 44), (67, 21),
    (197, 16), (123, 47), (197, 52), (123, 45),
    (47, 34), (80, 34), (47, 54), (80, 28),
    (110, 48), (190, 47), (110, 50), (190, 45),
    (197, 8), (123, 55), (197, 44), (123, 53),
    (226, 16), (67, 63), (226, 52), (67, 23),
    (110, 36), (190, 59), (110, 38), (190, 57),
    (47, 32), (80, 32), (47, 52), (80, 30),
    (67, 41), (226, 54), (67, 1), (226, 18),
    (123, 11), (197, 46), (123, 9), (197, 10),
    (80, 54), (47, 28), (80, 8), (47, 8),
    (190, 14), (110, 14), (190, 12), (110, 12),
    (123, 19), (197, 54), (123, 17), (197, 18),
    (67, 43), (226, 46), (67, 3), (226, 10),
    (190, 26), (110, 26), (190, 24), (110, 24),
    (80, 52), (47, 30), (80, 10), (47, 10)]

/-- Preferred source-Q masks, to be checked against the actual original inverse lattice matrix -/
def generatedSixthXiOctadPacket00SourceMasks : Fin 64 → Fin 4096 × Fin 4096 :=
  ![(3, 1027), (2051, 336), (2051, 1392), (2051, 35),
    (2051, 1344), (2051, 19), (2051, 1075), (3, 352),
    (2051, 1376), (2051, 51), (2051, 1043), (3, 320),
    (2051, 1059), (3, 368), (3, 1360), (3, 3),
    (2051, 339), (2051, 1024), (2051, 32), (3, 1395),
    (2051, 16), (3, 1347), (3, 355), (3, 1072),
    (2051, 48), (3, 1379), (3, 323), (3, 1040),
    (3, 371), (3, 1056), (3, 0), (2051, 1363),
    (2051, 2035), (2051, 672), (2051, 1664), (3, 979),
    (2051, 1712), (3, 995), (3, 1987), (3, 656),
    (2051, 1680), (3, 963), (3, 2019), (3, 688),
    (3, 2003), (3, 640), (3, 1696), (2051, 1011),
    (2051, 675), (3, 2032), (3, 976), (3, 1667),
    (3, 992), (3, 1715), (3, 659), (2051, 1984),
    (3, 960), (3, 1683), (3, 691), (2051, 2016),
    (3, 643), (2051, 2000), (2051, 1008), (2051, 1699)]

/-- Physical global signs, kept separately from the full preferred-Q phases -/
def generatedSixthXiOctadPacket00PhysicalPhase : Fin 64 → ZMod 2 :=
  ![1, 0, 1, 0,
    1, 0, 1, 0,
    1, 1, 1, 0,
    1, 0, 1, 0,
    1, 0, 1, 0,
    1, 0, 1, 0,
    1, 0, 1, 0,
    1, 1, 1, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    1, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    1, 0, 0, 0]

/-- Full original preferred phases, requiring the original signed scalar evaluator certificate -/
def generatedSixthXiOctadPacket00Phase : Fin 64 → ZMod 2 :=
  ![1, 1, 0, 0,
    0, 0, 1, 1,
    0, 0, 1, 1,
    1, 1, 0, 0,
    0, 0, 1, 1,
    1, 1, 0, 0,
    1, 1, 0, 0,
    0, 0, 1, 1,
    0, 0, 1, 1,
    1, 1, 0, 0,
    1, 1, 0, 0,
    0, 0, 1, 1,
    1, 1, 0, 0,
    0, 0, 1, 1,
    0, 0, 1, 1,
    1, 1, 0, 0]

/-- The genuine source family corresponding to original code 3. -/
def generatedSixthXiOctadPacket00Input (e : Fin 64) : GriessShortIndex :=
  Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad 190, e))

/-- The genuine cached preferred output label. -/
def generatedSixthXiOctadPacket00Output (e : Fin 64) : GriessShortIndex :=
  let x := generatedSixthXiOctadPacket00OutputAddress e
  Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad x.1, x.2))

/-- Complete original preferred input integer vector. -/
def generatedSixthXiOctadPacket00InputIntegral (e : Fin 64) : Fin 24 → ℤ :=
  generatedSixthMonomialOctadIntegral 190 e

/-- Complete original preferred output integer vector. -/
def generatedSixthXiOctadPacket00OutputIntegral (e : Fin 64) : Fin 24 → ℤ :=
  let x := generatedSixthXiOctadPacket00OutputAddress e
  generatedSixthMonomialOctadIntegral x.1 x.2

/-- The executable input is the original intrinsic preferred integer vector. -/
theorem generatedSixth_xi_octad_packet00_input_integral (e : Fin 64) :
    griessShortIntegral (generatedSixthXiOctadPacket00Input e) =
      generatedSixthXiOctadPacket00InputIntegral e := by
  funext i
  exact generatedSixth_monomial_octad_integral _ _ i

/-- The executable output is the original intrinsic preferred integer vector. -/
theorem generatedSixth_xi_octad_packet00_output_integral (e : Fin 64) :
    griessShortIntegral (generatedSixthXiOctadPacket00Output e) =
      generatedSixthXiOctadPacket00OutputIntegral e := by
  funext i
  exact generatedSixth_monomial_octad_integral _ _ i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
