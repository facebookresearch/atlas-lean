/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelMonomialMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Every original root-kernel word is retained through the nine actual monomial candidates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Index the five physical sign candidates followed by four original pure permutation candidates. -/
def generatedTwelfthCertifiedKernelIndex (g : Fin 9) : Fin 12 := ⟨g.val + 3, by omega⟩

/-- Every finite original candidate sign on every physical coordinate. -/
def generatedTwelfthCertifiedKernelLetterSign (g : Fin 9) (i : Fin 24) : ZMod 2 :=
  if h : g.val < 5 then
    (sourceGeneratedSignCode
      (generatedTwelfthRootKernelSignLabel ⟨2 ^ g.val, by
        fin_cases g <;> norm_num at h <;> norm_num⟩)).val i
  else 0

/-- Every complete physical pullback of all nine actual monomial candidate letters. -/
def generatedTwelfthCertifiedKernelLetterBackward (g : Fin 9) (i : Fin 24) : Fin 24 :=
  if h : g.val < 5 then i else
    generatedTwelfthRootKernelPermutationBackward
      ⟨2 ^ (g.val - 5), by
        fin_cases g <;> norm_num at h <;> norm_num⟩ i

/-- Whole original sign words in the five genuine independent physical sign candidates. -/
def generatedTwelfthCertifiedKernelSignWord : Fin 32 → List (Fin 9) :=
  ![[], [0], [1], [0, 1], [2], [0, 2], [1, 2], [0, 1, 2], [3], [0, 3], [1, 3], [0, 1, 3], [2, 3], [0, 2, 3], [1, 2, 3], [0, 1, 2, 3], [4], [0, 4], [1, 4], [0, 1, 4], [2, 4], [0, 2, 4], [1, 2, 4], [0, 1, 2, 4], [3, 4], [0, 3, 4], [1, 3, 4], [0, 1, 3, 4], [2, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4]]

/-- Whole original permutation words in the four genuine pointwise-octad candidates. -/
def generatedTwelfthCertifiedKernelPermutationWord : Fin 16 → List (Fin 9) :=
  ![[], [5], [6], [5, 6], [7], [5, 6, 7], [5, 7], [6, 7], [8], [6, 8], [5, 6, 8], [5, 8], [7, 8], [5, 7, 8], [6, 7, 8], [5, 6, 7, 8]]

/-- Exact whole monomial word evaluation on every original physical coordinate. -/
def generatedTwelfthCertifiedKernelWordData : List (Fin 9) → Fin 24 → ZMod 2 × Fin 24
  | [], i => (0, i)
  | g :: w, i =>
      let u := generatedTwelfthCertifiedKernelWordData w
        (generatedTwelfthCertifiedKernelLetterBackward g i)
      (generatedTwelfthCertifiedKernelLetterSign g i + u.1, u.2)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
