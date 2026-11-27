/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessStep

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessStep

open MetaMathlibExt

private def P : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 3]

private def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 2]

private def R : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

private theorem triple111 : IsGenCohnTriple 0 P Q R 1 1 1 :=
  ⟨⟨by decide, 1, by decide, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩,
    ⟨by decide, 1, by decide, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩,
    ⟨by decide, 1, by decide, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩,
    by decide, by decide, by decide, by decide, isGenMarkovTriple_one_one_one 0⟩

-- Both children of the `(1, 1, 1)` triple are `(1, 2, 1)` triples.
example : IsGenCohnTriple 0 P (P * Q - genCohnS 0) Q 1 2 1 ∧
    IsGenCohnTriple 0 Q (Q * R - genCohnS 0) R 1 2 1 :=
  IsGenCohnTriple.step triple111

-- The left child gives the Markov triple `(1, 2, 1)`.
example : IsGenMarkovTriple 0 1 2 1 :=
  (IsGenCohnTriple.step triple111).1.2.2.2.2.2.2.2

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessStep
