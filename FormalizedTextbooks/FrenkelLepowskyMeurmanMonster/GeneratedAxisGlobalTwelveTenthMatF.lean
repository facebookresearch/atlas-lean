/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Fast integer matrix blocks for long monomial words

The integer spatial action `wordZ` (worker gident2) reads the monomial coordinate permutations
from `![..]` tables, which costs up to a fraction of a second per lookup in the kernel; words with
long monomial runs (seventy letters, twenty-two rank-one terms) are then out of reach.  `wordZF`
reads the four monomial permutations from one packed table (`monoIdxF`, checked once against
`monoPermIdx`); `MatZ.actF_eq` makes it a drop-in for `MatZ.act`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

set_option linter.style.longLine false in
/-- The four monomial coordinate permutations in `5`-bit fields: table `2 k + b` for the letter
`(k, b)`, entry `i` at field `24 (2 k + b) + i`. -/
def monoTabP : ℕ :=
  0xb5eb09ca347ace3728c26a4a162080b5eb09ca347ace3728c26a4a162080b862d14ece9540c525072988b8506fbc5c293ea30428c22d49418e50cecd

/-- The coordinate read by a monomial letter, from the packed table. -/
def monoIdxF (l : Fin 2 × Bool) (i : ℕ) : ℕ :=
  (monoTabP >>> (5 * (24 * (2 * l.1.val + (if l.2 then 1 else 0)) + i))) &&& 31

set_option maxRecDepth 100000 in
/-- The packed table is the monomial coordinate permutation. -/
theorem monoIdxF_eq : ∀ (l : Fin 2 × Bool) (i : Fin 24),
    monoIdxF l i.val = (monoPermIdx l i).val := by
  decide +kernel

/-- Integer monomial source letter from the packed table. -/
def monoZF (l : Fin 2 × Bool) (z : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin 24 => zget z (monoIdxF l i.val))

theorem monoZF_eq (l : Fin 2 × Bool) (z : List ℤ) : monoZF l z = monoZ l z := by
  unfold monoZF monoZ
  congr 1
  funext i
  rw [monoIdxF_eq]

/-- Integer spatial action of a letter, monomial letters from the packed table. -/
def letterZF : IdentLetter → List ℤ → List ℤ
  | .mono l, z => monoZF l z
  | x, z => letterZ x z

theorem letterZF_eq (x : IdentLetter) (z : List ℤ) : letterZF x z = letterZ x z := by
  cases x with
  | mono l => exact monoZF_eq l z
  | xi => rfl
  | sign a ε => rfl
  | qel g => rfl

/-- Integer spatial action of a word with the packed monomial tables. -/
def wordZF : List IdentLetter → List ℤ → List ℤ
  | [], z => z
  | x :: w, z => letterZF x (wordZF w z)

theorem wordZF_eq : ∀ (w : List IdentLetter) (z : List ℤ), wordZF w z = wordZ w z
  | [], _ => rfl
  | x :: w, z => by rw [wordZF, wordZ, wordZF_eq w z, letterZF_eq]

/-- The integer matrix block transported by a word, with the packed monomial tables. -/
def MatZ.actF (w : List IdentLetter) (M : MatZ) : MatZ :=
  ⟨M.scal, M.den, M.terms.map (fun t => (t.1, wordZF w t.2)), M.k + wordE w⟩

theorem MatZ.actF_eq (w : List IdentLetter) (M : MatZ) : M.actF w = M.act w := by
  unfold MatZ.actF MatZ.act
  simp only [wordZF_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
