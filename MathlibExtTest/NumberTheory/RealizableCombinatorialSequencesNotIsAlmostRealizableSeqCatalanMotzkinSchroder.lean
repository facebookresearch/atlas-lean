/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RealizableCombinatorialSequencesNotIsAlmostRealizableSeqCatalanMotzkinSchroder

/-!
# Concrete multiples of Catalan, Motzkin and large Schröder sequences

Tests that multipliers one, two and three cannot make the respective sequences Dold realizable.
-/

namespace MathlibExtTest.NumberTheory.RealizableCombinatorialSequencesNotIsAlmostRealizableSeqCatalanMotzkinSchroder

open MetaMathlibExt

example : ¬ doldRealizable (fun n => ((catalan n : ℕ) : ℤ)) := by
  intro h
  exact not_isAlmostRealizableSeq_catalan_motzkin_schroder.1
    ⟨1, by decide, by simpa using h⟩

example : ¬ doldRealizable (fun n => ((2 * motzkinNumber n : ℕ) : ℤ)) := by
  intro h
  exact not_isAlmostRealizableSeq_catalan_motzkin_schroder.2.1 ⟨2, by decide, h⟩

example : ¬ doldRealizable (fun n => ((3 * Nat.largeSchroder n : ℕ) : ℤ)) := by
  intro h
  exact not_isAlmostRealizableSeq_catalan_motzkin_schroder.2.2 ⟨3, by decide, h⟩

end MathlibExtTest.NumberTheory.RealizableCombinatorialSequencesNotIsAlmostRealizableSeqCatalanMotzkinSchroder
