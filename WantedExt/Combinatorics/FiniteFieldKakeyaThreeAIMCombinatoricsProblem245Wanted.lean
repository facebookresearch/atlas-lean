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
/-- Tao's question (AIM, Recent trends in additive combinatorics, Problem 3.8) in Dvir's form: there
is `c > 0` such that every Kakeya set `E ⊆ F³` over a finite field `F` (a set containing a line in
every direction, `IsKakeya` of `FraserKakeyaWanted`) has `|E| ≥ c |F|³`, an exponent `3 > 5/2`. -/
def finiteFieldKakeyaCubeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (E : Finset (Fin 3 → F)),
    IsKakeya (F := F) (d := 3) (E : Set (Fin 3 → F)) → c * (Fintype.card F : ℝ) ^ 3 ≤ E.card

/--
Resolved true, with the optimal exponent `3`: Dvir proved by the polynomial method that every Kakeya
set `K ⊆ Fⁿ` over a finite field with `q` elements has `|K| ≥ C_n qⁿ` (Theorem 3, the Alon-Tao form
of his Theorem 1); for `n = 3` this is `|E| ≫ |F|³`, beyond Wolff's `|F|^{5/2}` by `ε = 1/2`.
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.8 (T. Tao);
resolution: Z. Dvir, On the size of Kakeya sets in finite fields, J. Amer. Math. Soc. 22 (2009),
1093-1097, arXiv:0803.2336, Theorem 3 (Section 1.1, the Alon-Tao improvement of Theorem 1): every
Kakeya set K ⊂ Fⁿ satisfies |K| ≥ C_n qⁿ with C_n depending only on n; for n = 3 this is |K| ≫ q³,
https://doi.org/10.1090/S0894-0347-08-00607-3.
-/
public theorem_wanted finiteFieldKakeyaCubeLowerBound_holds : finiteFieldKakeyaCubeLowerBound

end MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted
