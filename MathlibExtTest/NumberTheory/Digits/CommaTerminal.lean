/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.CommaTerminal

open MetaMathlibExt

-- The terminal pattern needs no leading copies of the maximal digit in `18`.
example : IsCommaTerminal 10 18 :=
  (isCommaTerminal_iff_digits 10 18 (by decide) (by decide)).2 ⟨0, 1, by decide, by decide, rfl⟩

example : IsCommaTerminal 10 918 :=
  (isCommaTerminal_iff_digits 10 918 (by decide) (by decide)).2 ⟨1, 1, by decide, by decide, rfl⟩

-- `4` is `11` in base three, the smallest base with any terminal numbers.
example : IsCommaTerminal 3 4 :=
  (isCommaTerminal_iff_digits 3 4 (by decide) (by decide)).2 ⟨0, 1, by decide, by decide, rfl⟩

example (n : ℕ) (hn : 0 < n) : ¬ IsCommaTerminal 2 n := by
  intro h
  obtain ⟨_, x, hx₁, hx₂, _⟩ := (isCommaTerminal_iff_digits 2 n (by decide) hn).1 h
  omega

-- At `15`, the leading digit of `65` is `6`, but `65 + 6` has leading digit `7`.
example : ¬ IsCommaTerminal 10 15 := by
  intro h
  refine h ⟨7, by decide⟩ ?_
  unfold IsCommaCandidate commaMsd
  decide

-- For `9`, the candidate digit `1` carries from `99` to `100`.
example : ¬ IsCommaTerminal 10 9 := by
  intro h
  refine h ⟨1, by decide⟩ ?_
  unfold IsCommaCandidate commaMsd
  decide

-- For `19`, the candidate digit `1` gives `110`.
example : ¬ IsCommaTerminal 10 19 := by
  intro h
  refine h ⟨1, by decide⟩ ?_
  unfold IsCommaCandidate commaMsd
  decide
