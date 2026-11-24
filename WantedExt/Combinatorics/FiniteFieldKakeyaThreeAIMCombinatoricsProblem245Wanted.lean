/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kakeya sets in F³ over finite fields have size ≫ |F|³ (AIM additive combinatorics, Problem 3.8)

AIM workshop Recent trends in additive combinatorics, Problem 3.8 (T. Tao): let `F` be a finite
field and `E ⊆ F × F × F` a Besicovitch set, i.e. `E` contains a line in every direction. It is
known from the work of Wolff that `|E| ≳ |F|^{5/2}`; prove the better lower bound `|E| ≳ |F|^{5/2 +
ε}`.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.FraserKakeyaWanted

@[expose] public section

namespace MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.8 (T. Tao).
UnsolvedMath record UM-20001120 (`AIM-COMBINATORICS-0245`), dataset ulamai/UnsolvedMath v1.8.0.

Kakeya (Besicovitch) sets are `IsKakeya` of `FraserKakeyaWanted` in dimension `3`: for every vector
`x` some line `{y + a x}` lies in the set. The statement is Dvir's bound `|E| ≥ c |F|³` with one
absolute `c > 0`, which gives the requested `5/2 + ε` with `ε = 1/2`.
-/

open MathlibExt.Combinatorics.FraserKakeyaWanted.Combinatorics.FraserKakeyaProblem in
/-- **Statement of the finite field Kakeya bound in dimension three.** This is the statement that
there is a real number $c > 0$ such that for every finite field $F$ and every Kakeya set
$E \subseteq F^3$, that is, a set such that for every $x \in F^3$ there is $y \in F^3$ with
$\{y + a x : a \in F\} \subseteq E$, we have $|E| \ge c\,|F|^3$.

This is Dvir's form of Tao's question (AIM, Recent trends in additive combinatorics, Problem 3.8),
which asks for $|E| \gtrsim |F|^{5/2 + \varepsilon}$ for some $\varepsilon > 0$; the exponent $3$
gives $\varepsilon = 1/2$. -/
def finiteFieldKakeyaCubeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (E : Finset (Fin 3 → F)),
    IsKakeya (F := F) (d := 3) (E : Set (Fin 3 → F)) → c * (Fintype.card F : ℝ) ^ 3 ≤ E.card

/--
**Finite field Kakeya sets in dimension three have cubic size.** There is a real number $c > 0$
such that for every finite field $F$ and every Kakeya set $E \subseteq F^3$, that is, a set such
that for every $x \in F^3$ there is $y \in F^3$ with $\{y + a x : a \in F\} \subseteq E$, we have
$|E| \ge c\,|F|^3$.

Dvir proved by the polynomial method that every Kakeya set $K \subseteq F^n$ over a finite field
$F$ with $q$ elements has $|K| \ge C_n q^n$, with $C_n$ depending only on $n$ (Theorem 3, the
Alon–Tao form of his Theorem 1). For $n = 3$ this answers Tao's question, which asks for
$|E| \gtrsim |F|^{5/2 + \varepsilon}$ for some $\varepsilon > 0$, beyond Wolff's bound
$|F|^{5/2}$, with $\varepsilon = 1/2$.

Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.8 (T. Tao);
resolution: Z. Dvir, On the size of Kakeya sets in finite fields, J. Amer. Math. Soc. 22 (2009),
1093-1097, arXiv:0803.2336, Theorem 3 (Section 1.1, the Alon-Tao improvement of Theorem 1): every
Kakeya set K ⊂ Fⁿ satisfies |K| ≥ C_n qⁿ with C_n depending only on n; for n = 3 this is |K| ≫ q³,
https://doi.org/10.1090/S0894-0347-08-00607-3.
-/
public theorem_wanted finiteFieldKakeyaCubeLowerBound_holds : finiteFieldKakeyaCubeLowerBound

end MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted
