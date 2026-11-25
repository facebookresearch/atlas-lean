/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- **Stark–Heegner theorem.** Let $d$ be a positive squarefree integer and let $K$ be a number
field of degree $2$ over $\mathbb{Q}$ that contains an element $x$ with $x^2 = -d$, so that
$K = \mathbb{Q}(\sqrt{-d})$. Then $K$ has class number $1$ if and only if
$d \in \{1, 2, 3, 7, 11, 19, 43, 67, 163\}$.

Source: K. Heegner, *Diophantische Analysis und Modulfunktionen*,
Mathematische Zeitschrift 56 (1952), 227–253; A. Baker, *Linear forms in the
logarithms of algebraic numbers*, Mathematika 13–15 (1966–1968); H. M. Stark,
*A complete determination of the complex quadratic fields of class-number one*,
Michigan Mathematical Journal 14 (1967), 1–27; see also
https://en.wikipedia.org/wiki/Stark%E2%80%93Heegner_theorem. -/
theorem_wanted stark_heegner_theorem (d : ℕ) (hd_pos : 0 < d) (hd_sf : Squarefree d)
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2)
    (hsqrt : ∃ x : K, x ^ 2 = algebraMap ℚ K (-(d : ℚ))) :
    NumberField.classNumber K = 1 ↔
    d ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)

end MetaMathlibExt

end
