/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Init
public import Mathlib.Data.ZMod.Basic

/-!
# Residues of rational numbers modulo an integer

This file defines `MetaMathlibExt.ratResidue m x`, the element `a * b⁻¹` of `ZMod m` attached to
a rational number `x = a / b` in lowest terms. When `b` is prime to `m`, it is the residue modulo
`m` of `x` viewed in the ring of rational numbers whose denominator is prime to `m`, so congruences
between such rational numbers can be stated as equalities in `ZMod m`.

`MathlibExt.NumberTheory.GobelSequence` re-exports the definition and its value on integers.

## Main definitions

* `MetaMathlibExt.ratResidue`: the residue modulo `m` of a rational number.

## Main statements

* `MetaMathlibExt.ratResidue_intCast`: on integers, the residue is the usual cast to `ZMod m`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Residue of a rational number modulo an integer.** For a natural number $m$ and a rational
number $x = a/b$ in lowest terms with $b > 0$, the residue of $x$ modulo $m$ is the element
$a \cdot b^{-1}$ of $\mathbb{Z}/m\mathbb{Z}$. When $b$ is prime to $m$, $b^{-1}$ is the inverse
of $b$ modulo $m$, so the residue is the class $c$ with $b c \equiv a \pmod m$; for other $x$
the inverse, and hence the residue, is a conventional value with no arithmetic meaning.

For a prime $p$ and a natural number $r$, it is used to read congruences modulo $p^r$ in the
ring $\mathbb{Z}_{(p)}$ of rational numbers whose denominator is prime to $p$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4 (residues of `g_{k,l}(n)` modulo `p^r` in `ℤ_(p)`). -/
public def ratResidue (m : ℕ) (x : ℚ) : ZMod m :=
  (x.num : ZMod m) * (x.den : ZMod m)⁻¹

/-- **Residue of an integer.** For every natural number $m$ and every integer $z$, the residue
modulo $m$ of $z$, viewed as a rational number, is the image of $z$ in $\mathbb{Z}/m\mathbb{Z}$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 4. -/
public theorem ratResidue_intCast (m : ℕ) (z : ℤ) : ratResidue m z = (z : ZMod m) := by
  simp [ratResidue]

end

end MetaMathlibExt
