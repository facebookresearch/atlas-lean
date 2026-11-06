/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheData

/-! Exact inverse full-Q data for the four genuine original Fourth frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFourthInverseMaskColumns : Fin 4 → Fin 24 → ℕ :=
  ![![9875153, 12943527, 16172848, 5652184, 4965588, 6729018, 1787978, 12998889, 3049364, 13138091, 4576378, 4849664, 8249695, 5388637, 4265984, 6445143, 2091359, 3504388, 1771532, 6211584, 8298760, 7995394, 4886619, 10686778],
    ![2238740, 5945028, 694167, 217116, 7340817, 8302027, 7790486, 13699193, 14349908, 2422799, 14949247, 4851712, 6936927, 4397070, 7932253, 5161047, 6295816, 4118792, 4636763, 7782400, 4718592, 1445979, 4114432, 7171748],
    ![9080768, 2240860, 3160749, 5030909, 5552589, 5288666, 1966288, 15077289, 4839773, 3619826, 1093844, 4196352, 1771520, 133129, 1378314, 7, 6160384, 3737600, 655372, 1769472, 3, 788493, 3934220, 6864329],
    ![13241287, 2277727, 7350958, 797681, 5513673, 1092318, 1966288, 15111081, 4792671, 7855089, 1093840, 4194304, 5965824, 4364297, 5613578, 32775, 1968128, 7931904, 704524, 1769472, 12291, 4990989, 8177676, 15242701]]

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFourthInverseMaskPhases : Fin 4 → Fin 24 → ZMod 2 :=
  ![![0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1]]

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFourthInverseMaskRows : Fin 4 → Fin 24 → ℕ :=
  ![![6930744, 5951704, 9429624, 15901312, 9646784, 16062144, 13971456, 8934912, 1345024, 11038720, 1257472, 8388608, 2105344, 11730944, 8388608, 12976128, 10485760, 11796480, 13631488, 8388608, 6291456, 0, 0, 0],
    ![2406322, 10766220, 238840, 61600, 217152, 2376128, 2414080, 6684160, 15126016, 208896, 12744704, 8388608, 2588672, 0, 10977280, 196608, 2359296, 2359296, 8388608, 0, 0, 8388608, 0, 0],
    ![8789594, 10511260, 2122376, 58784, 12846688, 4456704, 8388736, 14842880, 3163136, 10510336, 12845056, 8388608, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 8388608, 0],
    ![6518364, 57520, 1097744, 1097888, 9487808, 7643904, 8388736, 3651328, 1097728, 3162112, 12845056, 8388608, 8388608, 13942784, 7634944, 14942208, 8388608, 8388608, 8388608, 0, 10485760, 8388608, 0, 0]]

/-- Full original inverse central linear correction coefficients. -/
def generatedAxisGlobalOddFourthInverseMaskCoefficients : Fin 4 → ℕ :=
  ![11350710, 14145272, 8626062, 11703337]

/-- The full inverse generator candidate retains its actual central bit. -/
def generatedAxisGlobalOddFourthInverseMaskGenerator (k : Fin 4) (i : Fin 24) : Q :=
  qCentral (generatedAxisGlobalOddFourthInverseMaskPhases k i) *
    generatedAxisGlobalQMask (generatedAxisGlobalOddFourthInverseMaskColumns k i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
