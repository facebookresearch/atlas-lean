/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountTypes

/-! Finite convolution certificates for actual source coordinate choices.
Each layer certifies one additional coordinate, retaining all square sums
up to64 and all eight height residues. No lattice-vector count is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Add one prescribed source coordinate to a counting histogram. -/
def leechNormEightCountStep (m : Bool) (b : ZMod 2)
    (f : ℕ → ZMod 8 → ℕ) (q : ℕ) (h : ZMod 8) : ℕ :=
  ∑ a : Fin 17, if (leechNormEightCoordinate a : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * (b.val : ZMod 4) ∧
      (leechNormEightCoordinate a).natAbs ^ 2 ≤ q then
    f (q - (leechNormEightCoordinate a).natAbs ^ 2)
      (h - (leechNormEightCoordinate a : ZMod 8)) else 0

/-- Square/height histogram after0 coordinates of source residue0. -/
def leechNormEightLayer00Degree0 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after1 coordinates of source residue0. -/
def leechNormEightLayer00Degree1 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 2, 0, 0, 0] h else
  if q.val = 64 then ![2, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after2 coordinates of source residue0. -/
def leechNormEightLayer00Degree2 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 4, 0, 0, 0] h else
  if q.val = 32 then ![4, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 64 then ![4, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after3 coordinates of source residue0. -/
def leechNormEightLayer00Degree3 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 6, 0, 0, 0] h else
  if q.val = 32 then ![12, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 8, 0, 0, 0] h else
  if q.val = 64 then ![6, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after4 coordinates of source residue0. -/
def leechNormEightLayer00Degree4 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 8, 0, 0, 0] h else
  if q.val = 32 then ![24, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 32, 0, 0, 0] h else
  if q.val = 64 then ![24, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after5 coordinates of source residue0. -/
def leechNormEightLayer00Degree5 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 10, 0, 0, 0] h else
  if q.val = 32 then ![40, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 80, 0, 0, 0] h else
  if q.val = 64 then ![90, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after6 coordinates of source residue0. -/
def leechNormEightLayer00Degree6 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 12, 0, 0, 0] h else
  if q.val = 32 then ![60, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 160, 0, 0, 0] h else
  if q.val = 64 then ![252, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after7 coordinates of source residue0. -/
def leechNormEightLayer00Degree7 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 14, 0, 0, 0] h else
  if q.val = 32 then ![84, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 280, 0, 0, 0] h else
  if q.val = 64 then ![574, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after8 coordinates of source residue0. -/
def leechNormEightLayer00Degree8 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 16, 0, 0, 0] h else
  if q.val = 32 then ![112, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 448, 0, 0, 0] h else
  if q.val = 64 then ![1136, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after9 coordinates of source residue0. -/
def leechNormEightLayer00Degree9 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 18, 0, 0, 0] h else
  if q.val = 32 then ![144, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 672, 0, 0, 0] h else
  if q.val = 64 then ![2034, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after10 coordinates of source residue0. -/
def leechNormEightLayer00Degree10 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 20, 0, 0, 0] h else
  if q.val = 32 then ![180, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 960, 0, 0, 0] h else
  if q.val = 64 then ![3380, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after11 coordinates of source residue0. -/
def leechNormEightLayer00Degree11 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 22, 0, 0, 0] h else
  if q.val = 32 then ![220, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 1320, 0, 0, 0] h else
  if q.val = 64 then ![5302, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after12 coordinates of source residue0. -/
def leechNormEightLayer00Degree12 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 24, 0, 0, 0] h else
  if q.val = 32 then ![264, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 1760, 0, 0, 0] h else
  if q.val = 64 then ![7944, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after13 coordinates of source residue0. -/
def leechNormEightLayer00Degree13 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 26, 0, 0, 0] h else
  if q.val = 32 then ![312, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 2288, 0, 0, 0] h else
  if q.val = 64 then ![11466, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after14 coordinates of source residue0. -/
def leechNormEightLayer00Degree14 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 28, 0, 0, 0] h else
  if q.val = 32 then ![364, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 2912, 0, 0, 0] h else
  if q.val = 64 then ![16044, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after15 coordinates of source residue0. -/
def leechNormEightLayer00Degree15 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 30, 0, 0, 0] h else
  if q.val = 32 then ![420, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 3640, 0, 0, 0] h else
  if q.val = 64 then ![21870, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after16 coordinates of source residue0. -/
def leechNormEightLayer00Degree16 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 32, 0, 0, 0] h else
  if q.val = 32 then ![480, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 4480, 0, 0, 0] h else
  if q.val = 64 then ![29152, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after17 coordinates of source residue0. -/
def leechNormEightLayer00Degree17 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 34, 0, 0, 0] h else
  if q.val = 32 then ![544, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 5440, 0, 0, 0] h else
  if q.val = 64 then ![38114, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after18 coordinates of source residue0. -/
def leechNormEightLayer00Degree18 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 36, 0, 0, 0] h else
  if q.val = 32 then ![612, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 6528, 0, 0, 0] h else
  if q.val = 64 then ![48996, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after19 coordinates of source residue0. -/
def leechNormEightLayer00Degree19 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 38, 0, 0, 0] h else
  if q.val = 32 then ![684, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 7752, 0, 0, 0] h else
  if q.val = 64 then ![62054, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after20 coordinates of source residue0. -/
def leechNormEightLayer00Degree20 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 40, 0, 0, 0] h else
  if q.val = 32 then ![760, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 9120, 0, 0, 0] h else
  if q.val = 64 then ![77560, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after21 coordinates of source residue0. -/
def leechNormEightLayer00Degree21 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 42, 0, 0, 0] h else
  if q.val = 32 then ![840, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 10640, 0, 0, 0] h else
  if q.val = 64 then ![95802, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after22 coordinates of source residue0. -/
def leechNormEightLayer00Degree22 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 44, 0, 0, 0] h else
  if q.val = 32 then ![924, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 12320, 0, 0, 0] h else
  if q.val = 64 then ![117084, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after23 coordinates of source residue0. -/
def leechNormEightLayer00Degree23 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 46, 0, 0, 0] h else
  if q.val = 32 then ![1012, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 14168, 0, 0, 0] h else
  if q.val = 64 then ![141726, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after24 coordinates of source residue0. -/
def leechNormEightLayer00Degree24 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 48, 0, 0, 0] h else
  if q.val = 32 then ![1104, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 16192, 0, 0, 0] h else
  if q.val = 64 then ![170064, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after0 coordinates of source residue2. -/
def leechNormEightLayer01Degree0 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after1 coordinates of source residue2. -/
def leechNormEightLayer01Degree1 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 4 then ![0, 0, 1, 0, 0, 0, 1, 0] h else
  if q.val = 36 then ![0, 0, 1, 0, 0, 0, 1, 0] h else
  0

/-- Square/height histogram after2 coordinates of source residue2. -/
def leechNormEightLayer01Degree2 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 8 then ![2, 0, 0, 0, 2, 0, 0, 0] h else
  if q.val = 40 then ![4, 0, 0, 0, 4, 0, 0, 0] h else
  0

/-- Square/height histogram after3 coordinates of source residue2. -/
def leechNormEightLayer01Degree3 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 12 then ![0, 0, 4, 0, 0, 0, 4, 0] h else
  if q.val = 44 then ![0, 0, 12, 0, 0, 0, 12, 0] h else
  0

/-- Square/height histogram after4 coordinates of source residue2. -/
def leechNormEightLayer01Degree4 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 16 then ![8, 0, 0, 0, 8, 0, 0, 0] h else
  if q.val = 48 then ![32, 0, 0, 0, 32, 0, 0, 0] h else
  0

/-- Square/height histogram after5 coordinates of source residue2. -/
def leechNormEightLayer01Degree5 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 20 then ![0, 0, 16, 0, 0, 0, 16, 0] h else
  if q.val = 52 then ![0, 0, 80, 0, 0, 0, 80, 0] h else
  0

/-- Square/height histogram after6 coordinates of source residue2. -/
def leechNormEightLayer01Degree6 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 24 then ![32, 0, 0, 0, 32, 0, 0, 0] h else
  if q.val = 56 then ![192, 0, 0, 0, 192, 0, 0, 0] h else
  0

/-- Square/height histogram after7 coordinates of source residue2. -/
def leechNormEightLayer01Degree7 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 28 then ![0, 0, 64, 0, 0, 0, 64, 0] h else
  if q.val = 60 then ![0, 0, 448, 0, 0, 0, 448, 0] h else
  0

/-- Square/height histogram after8 coordinates of source residue2. -/
def leechNormEightLayer01Degree8 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 32 then ![128, 0, 0, 0, 128, 0, 0, 0] h else
  if q.val = 64 then ![1024, 0, 0, 0, 1024, 0, 0, 0] h else
  0

/-- Square/height histogram after9 coordinates of source residue2. -/
def leechNormEightLayer01Degree9 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 36 then ![0, 0, 256, 0, 0, 0, 256, 0] h else
  0

/-- Square/height histogram after10 coordinates of source residue2. -/
def leechNormEightLayer01Degree10 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 40 then ![512, 0, 0, 0, 512, 0, 0, 0] h else
  0

/-- Square/height histogram after11 coordinates of source residue2. -/
def leechNormEightLayer01Degree11 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 44 then ![0, 0, 1024, 0, 0, 0, 1024, 0] h else
  0

/-- Square/height histogram after12 coordinates of source residue2. -/
def leechNormEightLayer01Degree12 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 48 then ![2048, 0, 0, 0, 2048, 0, 0, 0] h else
  0

/-- Square/height histogram after13 coordinates of source residue2. -/
def leechNormEightLayer01Degree13 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 52 then ![0, 0, 4096, 0, 0, 0, 4096, 0] h else
  0

/-- Square/height histogram after14 coordinates of source residue2. -/
def leechNormEightLayer01Degree14 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 56 then ![8192, 0, 0, 0, 8192, 0, 0, 0] h else
  0

/-- Square/height histogram after15 coordinates of source residue2. -/
def leechNormEightLayer01Degree15 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 60 then ![0, 0, 16384, 0, 0, 0, 16384, 0] h else
  0

/-- Square/height histogram after16 coordinates of source residue2. -/
def leechNormEightLayer01Degree16 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 64 then ![32768, 0, 0, 0, 32768, 0, 0, 0] h else
  0

/-- Square/height histogram after17 coordinates of source residue2. -/
def leechNormEightLayer01Degree17 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after18 coordinates of source residue2. -/
def leechNormEightLayer01Degree18 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after19 coordinates of source residue2. -/
def leechNormEightLayer01Degree19 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after20 coordinates of source residue2. -/
def leechNormEightLayer01Degree20 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after21 coordinates of source residue2. -/
def leechNormEightLayer01Degree21 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after22 coordinates of source residue2. -/
def leechNormEightLayer01Degree22 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after23 coordinates of source residue2. -/
def leechNormEightLayer01Degree23 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after24 coordinates of source residue2. -/
def leechNormEightLayer01Degree24 (_q : Fin 65) (_h : Fin 8) : ℕ :=
  0

/-- Square/height histogram after0 coordinates of source residue1. -/
def leechNormEightLayer10Degree0 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after1 coordinates of source residue1. -/
def leechNormEightLayer10Degree1 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 1 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 9 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 25 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 49 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after2 coordinates of source residue1. -/
def leechNormEightLayer10Degree2 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 2 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 10 then ![0, 0, 0, 0, 0, 0, 2, 0] h else
  if q.val = 18 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 26 then ![0, 0, 0, 0, 0, 0, 2, 0] h else
  if q.val = 34 then ![0, 0, 2, 0, 0, 0, 0, 0] h else
  if q.val = 50 then ![0, 0, 3, 0, 0, 0, 0, 0] h else
  if q.val = 58 then ![0, 0, 0, 0, 0, 0, 2, 0] h else
  0

/-- Square/height histogram after3 coordinates of source residue1. -/
def leechNormEightLayer10Degree3 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 3 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 11 then ![0, 0, 0, 0, 0, 0, 0, 3] h else
  if q.val = 19 then ![0, 0, 0, 3, 0, 0, 0, 0] h else
  if q.val = 27 then ![0, 0, 0, 0, 0, 0, 0, 4] h else
  if q.val = 35 then ![0, 0, 0, 6, 0, 0, 0, 0] h else
  if q.val = 43 then ![0, 0, 0, 0, 0, 0, 0, 3] h else
  if q.val = 51 then ![0, 0, 0, 6, 0, 0, 0, 0] h else
  if q.val = 59 then ![0, 0, 0, 0, 0, 0, 0, 9] h else
  0

/-- Square/height histogram after4 coordinates of source residue1. -/
def leechNormEightLayer10Degree4 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 4 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 12 then ![4, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 20 then ![0, 0, 0, 0, 6, 0, 0, 0] h else
  if q.val = 28 then ![8, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 36 then ![0, 0, 0, 0, 13, 0, 0, 0] h else
  if q.val = 44 then ![12, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 52 then ![0, 0, 0, 0, 14, 0, 0, 0] h else
  if q.val = 60 then ![24, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after5 coordinates of source residue1. -/
def leechNormEightLayer10Degree5 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 5 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 13 then ![0, 5, 0, 0, 0, 0, 0, 0] h else
  if q.val = 21 then ![0, 0, 0, 0, 0, 10, 0, 0] h else
  if q.val = 29 then ![0, 15, 0, 0, 0, 0, 0, 0] h else
  if q.val = 37 then ![0, 0, 0, 0, 0, 25, 0, 0] h else
  if q.val = 45 then ![0, 31, 0, 0, 0, 0, 0, 0] h else
  if q.val = 53 then ![0, 0, 0, 0, 0, 35, 0, 0] h else
  if q.val = 61 then ![0, 55, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after6 coordinates of source residue1. -/
def leechNormEightLayer10Degree6 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 6 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 14 then ![0, 0, 6, 0, 0, 0, 0, 0] h else
  if q.val = 22 then ![0, 0, 0, 0, 0, 0, 15, 0] h else
  if q.val = 30 then ![0, 0, 26, 0, 0, 0, 0, 0] h else
  if q.val = 38 then ![0, 0, 0, 0, 0, 0, 45, 0] h else
  if q.val = 46 then ![0, 0, 66, 0, 0, 0, 0, 0] h else
  if q.val = 54 then ![0, 0, 0, 0, 0, 0, 82, 0] h else
  if q.val = 62 then ![0, 0, 120, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after7 coordinates of source residue1. -/
def leechNormEightLayer10Degree7 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 7 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 15 then ![0, 0, 0, 7, 0, 0, 0, 0] h else
  if q.val = 23 then ![0, 0, 0, 0, 0, 0, 0, 21] h else
  if q.val = 31 then ![0, 0, 0, 42, 0, 0, 0, 0] h else
  if q.val = 39 then ![0, 0, 0, 0, 0, 0, 0, 77] h else
  if q.val = 47 then ![0, 0, 0, 126, 0, 0, 0, 0] h else
  if q.val = 55 then ![0, 0, 0, 0, 0, 0, 0, 175] h else
  if q.val = 63 then ![0, 0, 0, 253, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after8 coordinates of source residue1. -/
def leechNormEightLayer10Degree8 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 8 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 8, 0, 0, 0] h else
  if q.val = 24 then ![28, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 32 then ![0, 0, 0, 0, 64, 0, 0, 0] h else
  if q.val = 40 then ![126, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 224, 0, 0, 0] h else
  if q.val = 56 then ![344, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 64 then ![0, 0, 0, 0, 512, 0, 0, 0] h else
  0

/-- Square/height histogram after9 coordinates of source residue1. -/
def leechNormEightLayer10Degree9 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 9 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 17 then ![0, 0, 0, 0, 0, 9, 0, 0] h else
  if q.val = 25 then ![0, 36, 0, 0, 0, 0, 0, 0] h else
  if q.val = 33 then ![0, 0, 0, 0, 0, 93, 0, 0] h else
  if q.val = 41 then ![0, 198, 0, 0, 0, 0, 0, 0] h else
  if q.val = 49 then ![0, 0, 0, 0, 0, 378, 0, 0] h else
  if q.val = 57 then ![0, 633, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after10 coordinates of source residue1. -/
def leechNormEightLayer10Degree10 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 10 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 18 then ![0, 0, 0, 0, 0, 0, 10, 0] h else
  if q.val = 26 then ![0, 0, 45, 0, 0, 0, 0, 0] h else
  if q.val = 34 then ![0, 0, 0, 0, 0, 0, 130, 0] h else
  if q.val = 42 then ![0, 0, 300, 0, 0, 0, 0, 0] h else
  if q.val = 50 then ![0, 0, 0, 0, 0, 0, 612, 0] h else
  if q.val = 58 then ![0, 0, 1105, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after11 coordinates of source residue1. -/
def leechNormEightLayer10Degree11 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 11 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 19 then ![0, 0, 0, 0, 0, 0, 0, 11] h else
  if q.val = 27 then ![0, 0, 0, 55, 0, 0, 0, 0] h else
  if q.val = 35 then ![0, 0, 0, 0, 0, 0, 0, 176] h else
  if q.val = 43 then ![0, 0, 0, 440, 0, 0, 0, 0] h else
  if q.val = 51 then ![0, 0, 0, 0, 0, 0, 0, 957] h else
  if q.val = 59 then ![0, 0, 0, 1848, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after12 coordinates of source residue1. -/
def leechNormEightLayer10Degree12 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 12 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 20 then ![12, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 28 then ![0, 0, 0, 0, 66, 0, 0, 0] h else
  if q.val = 36 then ![232, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 44 then ![0, 0, 0, 0, 627, 0, 0, 0] h else
  if q.val = 52 then ![1452, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 60 then ![0, 0, 0, 0, 2982, 0, 0, 0] h else
  0

/-- Square/height histogram after13 coordinates of source residue1. -/
def leechNormEightLayer10Degree13 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 13 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 21 then ![0, 13, 0, 0, 0, 0, 0, 0] h else
  if q.val = 29 then ![0, 0, 0, 0, 0, 78, 0, 0] h else
  if q.val = 37 then ![0, 299, 0, 0, 0, 0, 0, 0] h else
  if q.val = 45 then ![0, 0, 0, 0, 0, 871, 0, 0] h else
  if q.val = 53 then ![0, 2145, 0, 0, 0, 0, 0, 0] h else
  if q.val = 61 then ![0, 0, 0, 0, 0, 4667, 0, 0] h else
  0

/-- Square/height histogram after14 coordinates of source residue1. -/
def leechNormEightLayer10Degree14 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 14 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 22 then ![0, 0, 14, 0, 0, 0, 0, 0] h else
  if q.val = 30 then ![0, 0, 0, 0, 0, 0, 91, 0] h else
  if q.val = 38 then ![0, 0, 378, 0, 0, 0, 0, 0] h else
  if q.val = 46 then ![0, 0, 0, 0, 0, 0, 1183, 0] h else
  if q.val = 54 then ![0, 0, 3094, 0, 0, 0, 0, 0] h else
  if q.val = 62 then ![0, 0, 0, 0, 0, 0, 7112, 0] h else
  0

/-- Square/height histogram after15 coordinates of source residue1. -/
def leechNormEightLayer10Degree15 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 15 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 23 then ![0, 0, 0, 15, 0, 0, 0, 0] h else
  if q.val = 31 then ![0, 0, 0, 0, 0, 0, 0, 105] h else
  if q.val = 39 then ![0, 0, 0, 470, 0, 0, 0, 0] h else
  if q.val = 47 then ![0, 0, 0, 0, 0, 0, 0, 1575] h else
  if q.val = 55 then ![0, 0, 0, 4368, 0, 0, 0, 0] h else
  if q.val = 63 then ![0, 0, 0, 0, 0, 0, 0, 10585] h else
  0

/-- Square/height histogram after16 coordinates of source residue1. -/
def leechNormEightLayer10Degree16 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 16 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 24 then ![0, 0, 0, 0, 16, 0, 0, 0] h else
  if q.val = 32 then ![120, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 40 then ![0, 0, 0, 0, 576, 0, 0, 0] h else
  if q.val = 48 then ![2060, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 56 then ![0, 0, 0, 0, 6048, 0, 0, 0] h else
  if q.val = 64 then ![15424, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after17 coordinates of source residue1. -/
def leechNormEightLayer10Degree17 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 17 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 25 then ![0, 0, 0, 0, 0, 17, 0, 0] h else
  if q.val = 33 then ![0, 136, 0, 0, 0, 0, 0, 0] h else
  if q.val = 41 then ![0, 0, 0, 0, 0, 697, 0, 0] h else
  if q.val = 49 then ![0, 2652, 0, 0, 0, 0, 0, 0] h else
  if q.val = 57 then ![0, 0, 0, 0, 0, 8228, 0, 0] h else
  0

/-- Square/height histogram after18 coordinates of source residue1. -/
def leechNormEightLayer10Degree18 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 18 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 26 then ![0, 0, 0, 0, 0, 0, 18, 0] h else
  if q.val = 34 then ![0, 0, 153, 0, 0, 0, 0, 0] h else
  if q.val = 42 then ![0, 0, 0, 0, 0, 0, 834, 0] h else
  if q.val = 50 then ![0, 0, 3366, 0, 0, 0, 0, 0] h else
  if q.val = 58 then ![0, 0, 0, 0, 0, 0, 11016, 0] h else
  0

/-- Square/height histogram after19 coordinates of source residue1. -/
def leechNormEightLayer10Degree19 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 19 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 27 then ![0, 0, 0, 0, 0, 0, 0, 19] h else
  if q.val = 35 then ![0, 0, 0, 171, 0, 0, 0, 0] h else
  if q.val = 43 then ![0, 0, 0, 0, 0, 0, 0, 988] h else
  if q.val = 51 then ![0, 0, 0, 4218, 0, 0, 0, 0] h else
  if q.val = 59 then ![0, 0, 0, 0, 0, 0, 0, 14535] h else
  0

/-- Square/height histogram after20 coordinates of source residue1. -/
def leechNormEightLayer10Degree20 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 20 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 28 then ![20, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 36 then ![0, 0, 0, 0, 190, 0, 0, 0] h else
  if q.val = 44 then ![1160, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 52 then ![0, 0, 0, 0, 5225, 0, 0, 0] h else
  if q.val = 60 then ![18924, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after21 coordinates of source residue1. -/
def leechNormEightLayer10Degree21 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 21 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 29 then ![0, 21, 0, 0, 0, 0, 0, 0] h else
  if q.val = 37 then ![0, 0, 0, 0, 0, 210, 0, 0] h else
  if q.val = 45 then ![0, 1351, 0, 0, 0, 0, 0, 0] h else
  if q.val = 53 then ![0, 0, 0, 0, 0, 6405, 0, 0] h else
  if q.val = 61 then ![0, 24339, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after22 coordinates of source residue1. -/
def leechNormEightLayer10Degree22 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 22 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 30 then ![0, 0, 22, 0, 0, 0, 0, 0] h else
  if q.val = 38 then ![0, 0, 0, 0, 0, 0, 231, 0] h else
  if q.val = 46 then ![0, 0, 1562, 0, 0, 0, 0, 0] h else
  if q.val = 54 then ![0, 0, 0, 0, 0, 0, 7777, 0] h else
  if q.val = 62 then ![0, 0, 30954, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after23 coordinates of source residue1. -/
def leechNormEightLayer10Degree23 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 23 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 31 then ![0, 0, 0, 23, 0, 0, 0, 0] h else
  if q.val = 39 then ![0, 0, 0, 0, 0, 0, 0, 253] h else
  if q.val = 47 then ![0, 0, 0, 1794, 0, 0, 0, 0] h else
  if q.val = 55 then ![0, 0, 0, 0, 0, 0, 0, 9361] h else
  if q.val = 63 then ![0, 0, 0, 38962, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after24 coordinates of source residue1. -/
def leechNormEightLayer10Degree24 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 24 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 32 then ![0, 0, 0, 0, 24, 0, 0, 0] h else
  if q.val = 40 then ![276, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 2048, 0, 0, 0] h else
  if q.val = 56 then ![11178, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 64 then ![0, 0, 0, 0, 48576, 0, 0, 0] h else
  0

/-- Square/height histogram after0 coordinates of source residue3. -/
def leechNormEightLayer11Degree0 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 0 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after1 coordinates of source residue3. -/
def leechNormEightLayer11Degree1 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 1 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 9 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 25 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 49 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  0

/-- Square/height histogram after2 coordinates of source residue3. -/
def leechNormEightLayer11Degree2 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 2 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 10 then ![0, 0, 2, 0, 0, 0, 0, 0] h else
  if q.val = 18 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 26 then ![0, 0, 2, 0, 0, 0, 0, 0] h else
  if q.val = 34 then ![0, 0, 0, 0, 0, 0, 2, 0] h else
  if q.val = 50 then ![0, 0, 0, 0, 0, 0, 3, 0] h else
  if q.val = 58 then ![0, 0, 2, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after3 coordinates of source residue3. -/
def leechNormEightLayer11Degree3 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 3 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 11 then ![0, 3, 0, 0, 0, 0, 0, 0] h else
  if q.val = 19 then ![0, 0, 0, 0, 0, 3, 0, 0] h else
  if q.val = 27 then ![0, 4, 0, 0, 0, 0, 0, 0] h else
  if q.val = 35 then ![0, 0, 0, 0, 0, 6, 0, 0] h else
  if q.val = 43 then ![0, 3, 0, 0, 0, 0, 0, 0] h else
  if q.val = 51 then ![0, 0, 0, 0, 0, 6, 0, 0] h else
  if q.val = 59 then ![0, 9, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after4 coordinates of source residue3. -/
def leechNormEightLayer11Degree4 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 4 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 12 then ![4, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 20 then ![0, 0, 0, 0, 6, 0, 0, 0] h else
  if q.val = 28 then ![8, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 36 then ![0, 0, 0, 0, 13, 0, 0, 0] h else
  if q.val = 44 then ![12, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 52 then ![0, 0, 0, 0, 14, 0, 0, 0] h else
  if q.val = 60 then ![24, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after5 coordinates of source residue3. -/
def leechNormEightLayer11Degree5 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 5 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 13 then ![0, 0, 0, 0, 0, 0, 0, 5] h else
  if q.val = 21 then ![0, 0, 0, 10, 0, 0, 0, 0] h else
  if q.val = 29 then ![0, 0, 0, 0, 0, 0, 0, 15] h else
  if q.val = 37 then ![0, 0, 0, 25, 0, 0, 0, 0] h else
  if q.val = 45 then ![0, 0, 0, 0, 0, 0, 0, 31] h else
  if q.val = 53 then ![0, 0, 0, 35, 0, 0, 0, 0] h else
  if q.val = 61 then ![0, 0, 0, 0, 0, 0, 0, 55] h else
  0

/-- Square/height histogram after6 coordinates of source residue3. -/
def leechNormEightLayer11Degree6 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 6 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 14 then ![0, 0, 0, 0, 0, 0, 6, 0] h else
  if q.val = 22 then ![0, 0, 15, 0, 0, 0, 0, 0] h else
  if q.val = 30 then ![0, 0, 0, 0, 0, 0, 26, 0] h else
  if q.val = 38 then ![0, 0, 45, 0, 0, 0, 0, 0] h else
  if q.val = 46 then ![0, 0, 0, 0, 0, 0, 66, 0] h else
  if q.val = 54 then ![0, 0, 82, 0, 0, 0, 0, 0] h else
  if q.val = 62 then ![0, 0, 0, 0, 0, 0, 120, 0] h else
  0

/-- Square/height histogram after7 coordinates of source residue3. -/
def leechNormEightLayer11Degree7 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 7 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 15 then ![0, 0, 0, 0, 0, 7, 0, 0] h else
  if q.val = 23 then ![0, 21, 0, 0, 0, 0, 0, 0] h else
  if q.val = 31 then ![0, 0, 0, 0, 0, 42, 0, 0] h else
  if q.val = 39 then ![0, 77, 0, 0, 0, 0, 0, 0] h else
  if q.val = 47 then ![0, 0, 0, 0, 0, 126, 0, 0] h else
  if q.val = 55 then ![0, 175, 0, 0, 0, 0, 0, 0] h else
  if q.val = 63 then ![0, 0, 0, 0, 0, 253, 0, 0] h else
  0

/-- Square/height histogram after8 coordinates of source residue3. -/
def leechNormEightLayer11Degree8 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 8 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 16 then ![0, 0, 0, 0, 8, 0, 0, 0] h else
  if q.val = 24 then ![28, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 32 then ![0, 0, 0, 0, 64, 0, 0, 0] h else
  if q.val = 40 then ![126, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 224, 0, 0, 0] h else
  if q.val = 56 then ![344, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 64 then ![0, 0, 0, 0, 512, 0, 0, 0] h else
  0

/-- Square/height histogram after9 coordinates of source residue3. -/
def leechNormEightLayer11Degree9 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 9 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 17 then ![0, 0, 0, 9, 0, 0, 0, 0] h else
  if q.val = 25 then ![0, 0, 0, 0, 0, 0, 0, 36] h else
  if q.val = 33 then ![0, 0, 0, 93, 0, 0, 0, 0] h else
  if q.val = 41 then ![0, 0, 0, 0, 0, 0, 0, 198] h else
  if q.val = 49 then ![0, 0, 0, 378, 0, 0, 0, 0] h else
  if q.val = 57 then ![0, 0, 0, 0, 0, 0, 0, 633] h else
  0

/-- Square/height histogram after10 coordinates of source residue3. -/
def leechNormEightLayer11Degree10 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 10 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 18 then ![0, 0, 10, 0, 0, 0, 0, 0] h else
  if q.val = 26 then ![0, 0, 0, 0, 0, 0, 45, 0] h else
  if q.val = 34 then ![0, 0, 130, 0, 0, 0, 0, 0] h else
  if q.val = 42 then ![0, 0, 0, 0, 0, 0, 300, 0] h else
  if q.val = 50 then ![0, 0, 612, 0, 0, 0, 0, 0] h else
  if q.val = 58 then ![0, 0, 0, 0, 0, 0, 1105, 0] h else
  0

/-- Square/height histogram after11 coordinates of source residue3. -/
def leechNormEightLayer11Degree11 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 11 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 19 then ![0, 11, 0, 0, 0, 0, 0, 0] h else
  if q.val = 27 then ![0, 0, 0, 0, 0, 55, 0, 0] h else
  if q.val = 35 then ![0, 176, 0, 0, 0, 0, 0, 0] h else
  if q.val = 43 then ![0, 0, 0, 0, 0, 440, 0, 0] h else
  if q.val = 51 then ![0, 957, 0, 0, 0, 0, 0, 0] h else
  if q.val = 59 then ![0, 0, 0, 0, 0, 1848, 0, 0] h else
  0

/-- Square/height histogram after12 coordinates of source residue3. -/
def leechNormEightLayer11Degree12 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 12 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 20 then ![12, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 28 then ![0, 0, 0, 0, 66, 0, 0, 0] h else
  if q.val = 36 then ![232, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 44 then ![0, 0, 0, 0, 627, 0, 0, 0] h else
  if q.val = 52 then ![1452, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 60 then ![0, 0, 0, 0, 2982, 0, 0, 0] h else
  0

/-- Square/height histogram after13 coordinates of source residue3. -/
def leechNormEightLayer11Degree13 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 13 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 21 then ![0, 0, 0, 0, 0, 0, 0, 13] h else
  if q.val = 29 then ![0, 0, 0, 78, 0, 0, 0, 0] h else
  if q.val = 37 then ![0, 0, 0, 0, 0, 0, 0, 299] h else
  if q.val = 45 then ![0, 0, 0, 871, 0, 0, 0, 0] h else
  if q.val = 53 then ![0, 0, 0, 0, 0, 0, 0, 2145] h else
  if q.val = 61 then ![0, 0, 0, 4667, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after14 coordinates of source residue3. -/
def leechNormEightLayer11Degree14 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 14 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 22 then ![0, 0, 0, 0, 0, 0, 14, 0] h else
  if q.val = 30 then ![0, 0, 91, 0, 0, 0, 0, 0] h else
  if q.val = 38 then ![0, 0, 0, 0, 0, 0, 378, 0] h else
  if q.val = 46 then ![0, 0, 1183, 0, 0, 0, 0, 0] h else
  if q.val = 54 then ![0, 0, 0, 0, 0, 0, 3094, 0] h else
  if q.val = 62 then ![0, 0, 7112, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after15 coordinates of source residue3. -/
def leechNormEightLayer11Degree15 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 15 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 23 then ![0, 0, 0, 0, 0, 15, 0, 0] h else
  if q.val = 31 then ![0, 105, 0, 0, 0, 0, 0, 0] h else
  if q.val = 39 then ![0, 0, 0, 0, 0, 470, 0, 0] h else
  if q.val = 47 then ![0, 1575, 0, 0, 0, 0, 0, 0] h else
  if q.val = 55 then ![0, 0, 0, 0, 0, 4368, 0, 0] h else
  if q.val = 63 then ![0, 10585, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after16 coordinates of source residue3. -/
def leechNormEightLayer11Degree16 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 16 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 24 then ![0, 0, 0, 0, 16, 0, 0, 0] h else
  if q.val = 32 then ![120, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 40 then ![0, 0, 0, 0, 576, 0, 0, 0] h else
  if q.val = 48 then ![2060, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 56 then ![0, 0, 0, 0, 6048, 0, 0, 0] h else
  if q.val = 64 then ![15424, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after17 coordinates of source residue3. -/
def leechNormEightLayer11Degree17 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 17 then ![0, 0, 0, 0, 0, 0, 0, 1] h else
  if q.val = 25 then ![0, 0, 0, 17, 0, 0, 0, 0] h else
  if q.val = 33 then ![0, 0, 0, 0, 0, 0, 0, 136] h else
  if q.val = 41 then ![0, 0, 0, 697, 0, 0, 0, 0] h else
  if q.val = 49 then ![0, 0, 0, 0, 0, 0, 0, 2652] h else
  if q.val = 57 then ![0, 0, 0, 8228, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after18 coordinates of source residue3. -/
def leechNormEightLayer11Degree18 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 18 then ![0, 0, 0, 0, 0, 0, 1, 0] h else
  if q.val = 26 then ![0, 0, 18, 0, 0, 0, 0, 0] h else
  if q.val = 34 then ![0, 0, 0, 0, 0, 0, 153, 0] h else
  if q.val = 42 then ![0, 0, 834, 0, 0, 0, 0, 0] h else
  if q.val = 50 then ![0, 0, 0, 0, 0, 0, 3366, 0] h else
  if q.val = 58 then ![0, 0, 11016, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after19 coordinates of source residue3. -/
def leechNormEightLayer11Degree19 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 19 then ![0, 0, 0, 0, 0, 1, 0, 0] h else
  if q.val = 27 then ![0, 19, 0, 0, 0, 0, 0, 0] h else
  if q.val = 35 then ![0, 0, 0, 0, 0, 171, 0, 0] h else
  if q.val = 43 then ![0, 988, 0, 0, 0, 0, 0, 0] h else
  if q.val = 51 then ![0, 0, 0, 0, 0, 4218, 0, 0] h else
  if q.val = 59 then ![0, 14535, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after20 coordinates of source residue3. -/
def leechNormEightLayer11Degree20 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 20 then ![0, 0, 0, 0, 1, 0, 0, 0] h else
  if q.val = 28 then ![20, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 36 then ![0, 0, 0, 0, 190, 0, 0, 0] h else
  if q.val = 44 then ![1160, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 52 then ![0, 0, 0, 0, 5225, 0, 0, 0] h else
  if q.val = 60 then ![18924, 0, 0, 0, 0, 0, 0, 0] h else
  0

/-- Square/height histogram after21 coordinates of source residue3. -/
def leechNormEightLayer11Degree21 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 21 then ![0, 0, 0, 1, 0, 0, 0, 0] h else
  if q.val = 29 then ![0, 0, 0, 0, 0, 0, 0, 21] h else
  if q.val = 37 then ![0, 0, 0, 210, 0, 0, 0, 0] h else
  if q.val = 45 then ![0, 0, 0, 0, 0, 0, 0, 1351] h else
  if q.val = 53 then ![0, 0, 0, 6405, 0, 0, 0, 0] h else
  if q.val = 61 then ![0, 0, 0, 0, 0, 0, 0, 24339] h else
  0

/-- Square/height histogram after22 coordinates of source residue3. -/
def leechNormEightLayer11Degree22 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 22 then ![0, 0, 1, 0, 0, 0, 0, 0] h else
  if q.val = 30 then ![0, 0, 0, 0, 0, 0, 22, 0] h else
  if q.val = 38 then ![0, 0, 231, 0, 0, 0, 0, 0] h else
  if q.val = 46 then ![0, 0, 0, 0, 0, 0, 1562, 0] h else
  if q.val = 54 then ![0, 0, 7777, 0, 0, 0, 0, 0] h else
  if q.val = 62 then ![0, 0, 0, 0, 0, 0, 30954, 0] h else
  0

/-- Square/height histogram after23 coordinates of source residue3. -/
def leechNormEightLayer11Degree23 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 23 then ![0, 1, 0, 0, 0, 0, 0, 0] h else
  if q.val = 31 then ![0, 0, 0, 0, 0, 23, 0, 0] h else
  if q.val = 39 then ![0, 253, 0, 0, 0, 0, 0, 0] h else
  if q.val = 47 then ![0, 0, 0, 0, 0, 1794, 0, 0] h else
  if q.val = 55 then ![0, 9361, 0, 0, 0, 0, 0, 0] h else
  if q.val = 63 then ![0, 0, 0, 0, 0, 38962, 0, 0] h else
  0

/-- Square/height histogram after24 coordinates of source residue3. -/
def leechNormEightLayer11Degree24 (q : Fin 65) (h : Fin 8) : ℕ :=
  if q.val = 24 then ![1, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 32 then ![0, 0, 0, 0, 24, 0, 0, 0] h else
  if q.val = 40 then ![276, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 48 then ![0, 0, 0, 0, 2048, 0, 0, 0] h else
  if q.val = 56 then ![11178, 0, 0, 0, 0, 0, 0, 0] h else
  if q.val = 64 then ![0, 0, 0, 0, 48576, 0, 0, 0] h else
  0

/-- Complete bounded square/height histograms for powers of each coordinate series. -/
def leechNormEightCountTable (m : Bool) (b : ZMod 2) (n : Fin 25)
    (q : Fin 65) (h : ZMod 8) : ℕ :=
  if m = false then
    if b = 0 then ![
      leechNormEightLayer00Degree0,
      leechNormEightLayer00Degree1,
      leechNormEightLayer00Degree2,
      leechNormEightLayer00Degree3,
      leechNormEightLayer00Degree4,
      leechNormEightLayer00Degree5,
      leechNormEightLayer00Degree6,
      leechNormEightLayer00Degree7,
      leechNormEightLayer00Degree8,
      leechNormEightLayer00Degree9,
      leechNormEightLayer00Degree10,
      leechNormEightLayer00Degree11,
      leechNormEightLayer00Degree12,
      leechNormEightLayer00Degree13,
      leechNormEightLayer00Degree14,
      leechNormEightLayer00Degree15,
      leechNormEightLayer00Degree16,
      leechNormEightLayer00Degree17,
      leechNormEightLayer00Degree18,
      leechNormEightLayer00Degree19,
      leechNormEightLayer00Degree20,
      leechNormEightLayer00Degree21,
      leechNormEightLayer00Degree22,
      leechNormEightLayer00Degree23,
      leechNormEightLayer00Degree24] n q ⟨h.val, h.val_lt⟩
    else ![
      leechNormEightLayer01Degree0,
      leechNormEightLayer01Degree1,
      leechNormEightLayer01Degree2,
      leechNormEightLayer01Degree3,
      leechNormEightLayer01Degree4,
      leechNormEightLayer01Degree5,
      leechNormEightLayer01Degree6,
      leechNormEightLayer01Degree7,
      leechNormEightLayer01Degree8,
      leechNormEightLayer01Degree9,
      leechNormEightLayer01Degree10,
      leechNormEightLayer01Degree11,
      leechNormEightLayer01Degree12,
      leechNormEightLayer01Degree13,
      leechNormEightLayer01Degree14,
      leechNormEightLayer01Degree15,
      leechNormEightLayer01Degree16,
      leechNormEightLayer01Degree17,
      leechNormEightLayer01Degree18,
      leechNormEightLayer01Degree19,
      leechNormEightLayer01Degree20,
      leechNormEightLayer01Degree21,
      leechNormEightLayer01Degree22,
      leechNormEightLayer01Degree23,
      leechNormEightLayer01Degree24] n q ⟨h.val, h.val_lt⟩
  else
    if b = 0 then ![
      leechNormEightLayer10Degree0,
      leechNormEightLayer10Degree1,
      leechNormEightLayer10Degree2,
      leechNormEightLayer10Degree3,
      leechNormEightLayer10Degree4,
      leechNormEightLayer10Degree5,
      leechNormEightLayer10Degree6,
      leechNormEightLayer10Degree7,
      leechNormEightLayer10Degree8,
      leechNormEightLayer10Degree9,
      leechNormEightLayer10Degree10,
      leechNormEightLayer10Degree11,
      leechNormEightLayer10Degree12,
      leechNormEightLayer10Degree13,
      leechNormEightLayer10Degree14,
      leechNormEightLayer10Degree15,
      leechNormEightLayer10Degree16,
      leechNormEightLayer10Degree17,
      leechNormEightLayer10Degree18,
      leechNormEightLayer10Degree19,
      leechNormEightLayer10Degree20,
      leechNormEightLayer10Degree21,
      leechNormEightLayer10Degree22,
      leechNormEightLayer10Degree23,
      leechNormEightLayer10Degree24] n q ⟨h.val, h.val_lt⟩
    else ![
      leechNormEightLayer11Degree0,
      leechNormEightLayer11Degree1,
      leechNormEightLayer11Degree2,
      leechNormEightLayer11Degree3,
      leechNormEightLayer11Degree4,
      leechNormEightLayer11Degree5,
      leechNormEightLayer11Degree6,
      leechNormEightLayer11Degree7,
      leechNormEightLayer11Degree8,
      leechNormEightLayer11Degree9,
      leechNormEightLayer11Degree10,
      leechNormEightLayer11Degree11,
      leechNormEightLayer11Degree12,
      leechNormEightLayer11Degree13,
      leechNormEightLayer11Degree14,
      leechNormEightLayer11Degree15,
      leechNormEightLayer11Degree16,
      leechNormEightLayer11Degree17,
      leechNormEightLayer11Degree18,
      leechNormEightLayer11Degree19,
      leechNormEightLayer11Degree20,
      leechNormEightLayer11Degree21,
      leechNormEightLayer11Degree22,
      leechNormEightLayer11Degree23,
      leechNormEightLayer11Degree24] n q ⟨h.val, h.val_lt⟩

/-- Extend the bounded histogram by zero outside its certified norm range. -/
def leechNormEightCountTableNat (m : Bool) (b : ZMod 2) (n : Fin 25)
    (q : ℕ) (h : ZMod 8) : ℕ :=
  if hq : q < 65 then leechNormEightCountTable m b n ⟨q, hq⟩ h else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The empty-layer identity is checked on every bounded square/height state.
/-- The initial histogram counts only the empty assignment. -/
theorem leechNormEightCountTable_zero : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 0 q h = if q.val = 0 ∧ h = 0 then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step0 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 1 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 0) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step1 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 2 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 1) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step2 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 3 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 2) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step3 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 4 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 3) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step4 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 5 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 4) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step5 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 6 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 5) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step6 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 7 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 6) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step7 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 8 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 7) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step8 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 9 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 8) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step9 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 10 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 9) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step10 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 11 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 10) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step11 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 12 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 11) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step12 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 13 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 12) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step13 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 14 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 13) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step14 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 15 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 14) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step15 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 16 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 15) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step16 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 17 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 16) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step17 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 18 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 17) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step18 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 19 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 18) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step19 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 20 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 19) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step20 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 21 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 20) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step21 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 22 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 21) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step22 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 23 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 22) q.val h := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- One full layer checks both parities, both bits, and520 square/height states.
private theorem leechNormEightCountTable_step23 : ∀ m : Bool, ∀ b : ZMod 2,
    ∀ q : Fin 65, ∀ h : ZMod 8,
    leechNormEightCountTable m b 24 q h =
      leechNormEightCountStep m b (leechNormEightCountTableNat m b 23) q.val h := by
  decide +kernel

/-- Every stored successor histogram satisfies the actual coordinate recurrence. -/
theorem leechNormEightCountTable_step (m : Bool) (b : ZMod 2)
    (n : Fin 24) (q : Fin 65) (h : ZMod 8) :
    leechNormEightCountTable m b ⟨n.val + 1, by omega⟩ q h =
      leechNormEightCountStep m b
        (leechNormEightCountTableNat m b ⟨n.val, by omega⟩) q.val h := by
  fin_cases n
  · exact leechNormEightCountTable_step0 m b q h
  · exact leechNormEightCountTable_step1 m b q h
  · exact leechNormEightCountTable_step2 m b q h
  · exact leechNormEightCountTable_step3 m b q h
  · exact leechNormEightCountTable_step4 m b q h
  · exact leechNormEightCountTable_step5 m b q h
  · exact leechNormEightCountTable_step6 m b q h
  · exact leechNormEightCountTable_step7 m b q h
  · exact leechNormEightCountTable_step8 m b q h
  · exact leechNormEightCountTable_step9 m b q h
  · exact leechNormEightCountTable_step10 m b q h
  · exact leechNormEightCountTable_step11 m b q h
  · exact leechNormEightCountTable_step12 m b q h
  · exact leechNormEightCountTable_step13 m b q h
  · exact leechNormEightCountTable_step14 m b q h
  · exact leechNormEightCountTable_step15 m b q h
  · exact leechNormEightCountTable_step16 m b q h
  · exact leechNormEightCountTable_step17 m b q h
  · exact leechNormEightCountTable_step18 m b q h
  · exact leechNormEightCountTable_step19 m b q h
  · exact leechNormEightCountTable_step20 m b q h
  · exact leechNormEightCountTable_step21 m b q h
  · exact leechNormEightCountTable_step22 m b q h
  · exact leechNormEightCountTable_step23 m b q h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
