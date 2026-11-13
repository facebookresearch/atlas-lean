/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solubility and local finiteness of 4-Engel groups (Kourovka Notebook Problem 9.50)

Kourovka Notebook, Archive of Solved Problems, Problem 9.50 (Yu. P. Razmyslov): is every `4`-Engel
group a) without elements of order `2` and `5` necessarily soluble? b) satisfying the identity `x⁵ =
1` necessarily locally finite? c) (R. I. Grigorchuk) satisfying the identity `x⁸ = 1` necessarily
locally finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable
public import WantedExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted
public import WantedExt.GroupTheory.GroupClassesShared

@[expose] public section

namespace MathlibExt.GroupTheory.FourEngelGroupsKourovka9Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.50 (Yu. P.
Razmyslov). UnsolvedMath record UM-00700583 (`KOU-9.50`), dataset ulamai/UnsolvedMath v1.8.0.

A group is `4`-Engel if `[x, y, y, y, y] = 1` for all `x, y`, with left-normed commutators and `[u,
v] = u⁻¹ v⁻¹ u v` (`engelComm` of the 11.88 entry). "Without elements of order `2` and `5`" means no
element has order `2` or `5`. Locally finite is `IsLocallyFinite` of `GroupClassesShared`: every
finite subset generates a finite subgroup, i.e. every finitely generated subgroup is finite. One
target per part.
-/

open MathlibExt.GroupTheory.GroupClassesShared (IsLocallyFinite)
open MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted

/-- `G` is an `n`-Engel group: `[x, y; n] = 1` for all `x, y ∈ G`, with the left-normed Engel
commutator `engelComm` of the 11.88 entry (`[x, y; 0] = x`, `[x, y; l + 1] = [[x, y; l], y]`,
`[u, v] = u⁻¹ v⁻¹ u v`). -/
def IsEngelGroup (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ x y : G, engelComm x y n = 1

/-- Kourovka 9.50(a) (Yu. P. Razmyslov): every `4`-Engel group without elements of order `2` or `5`
is soluble. -/
def fourEngelNoTwoFiveSoluble : Prop :=
  ∀ (G : Type) [Group G], IsEngelGroup 4 G → (∀ g : G, orderOf g ≠ 2 ∧ orderOf g ≠ 5) →
    Group.IsSolvable G

/-- Kourovka 9.50(b) (Yu. P. Razmyslov): every `4`-Engel group satisfying `x⁵ = 1` is locally
finite. -/
def fourEngelExponentFiveLocallyFinite : Prop :=
  ∀ (G : Type) [Group G], IsEngelGroup 4 G → (∀ g : G, g ^ 5 = 1) → IsLocallyFinite G

/-- Kourovka 9.50(c) (R. I. Grigorchuk): every `4`-Engel group satisfying `x⁸ = 1` is locally
finite. -/
def fourEngelExponentEightLocallyFinite : Prop :=
  ∀ (G : Type) [Group G], IsEngelGroup 4 G → (∀ g : G, g ^ 8 = 1) → IsLocallyFinite G

/--
Resolved true: the Kourovka Archive answers 9.50(a) "Yes": `4`-Engel groups are locally nilpotent
(Traustason; Havas and Vaughan-Lee) and locally nilpotent `4`-Engel groups without elements of order
`2` or `5` are soluble (Abdollahi and Traustason). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 9.50 (Yu. P. Razmyslov); resolution: (a) G. Traustason, Two
generator 4-Engel groups, Internat. J. Algebra Comput. 15 (2005), 309-316; G. Havas and M. R.
Vaughan-Lee, 4-Engel groups are locally nilpotent, Internat. J. Algebra Comput. 15 (2005), 649-682;
A. Abdollahi and G. Traustason, On locally finite p-groups satisfying an Engel condition, Proc.
Amer. Math. Soc. 130 (2002), 2827-2836, https://doi.org/10.1090/S0002-9939-02-06421-3; (b) M. R.
Vaughan-Lee, Engel-4 groups of exponent 5, Proc. London Math. Soc. (3) 74 (1997), 306-334,
https://doi.org/10.1112/S0024611597000117; (c) G. Traustason, On 4-Engel groups, J. Algebra 178
(1995), 414-429, https://doi.org/10.1006/jabr.1995.1357, Kourovka Archive of Solved Problems,
Problem 9.50: a) Yes; this follows from the local nilpotency of 4-Engel groups (Traustason;
Havas-Vaughan-Lee) and the affirmative answer for locally nilpotent groups (Abdollahi-Traustason);
b) Yes, it is (Vaughan-Lee); c) Yes; moreover, every 4-Engel 2-group is locally finite (Traustason),
https://doi.org/10.1142/S0218196705002475.
-/
public theorem_wanted fourEngelNoTwoFiveSoluble_holds : fourEngelNoTwoFiveSoluble

/--
Resolved true: Vaughan-Lee proves that `4`-Engel groups of exponent `5` are locally finite; the
Kourovka Archive answers 9.50(b) "Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 9.50 (Yu. P. Razmyslov); resolution: (a) G. Traustason, Two
generator 4-Engel groups, Internat. J. Algebra Comput. 15 (2005), 309-316; G. Havas and M. R.
Vaughan-Lee, 4-Engel groups are locally nilpotent, Internat. J. Algebra Comput. 15 (2005), 649-682;
A. Abdollahi and G. Traustason, On locally finite p-groups satisfying an Engel condition, Proc.
Amer. Math. Soc. 130 (2002), 2827-2836, https://doi.org/10.1090/S0002-9939-02-06421-3; (b) M. R.
Vaughan-Lee, Engel-4 groups of exponent 5, Proc. London Math. Soc. (3) 74 (1997), 306-334,
https://doi.org/10.1112/S0024611597000117; (c) G. Traustason, On 4-Engel groups, J. Algebra 178
(1995), 414-429, https://doi.org/10.1006/jabr.1995.1357, Kourovka Archive of Solved Problems,
Problem 9.50: a) Yes; this follows from the local nilpotency of 4-Engel groups (Traustason;
Havas-Vaughan-Lee) and the affirmative answer for locally nilpotent groups (Abdollahi-Traustason);
b) Yes, it is (Vaughan-Lee); c) Yes; moreover, every 4-Engel 2-group is locally finite (Traustason),
https://doi.org/10.1142/S0218196705002475.
-/
public theorem_wanted fourEngelExponentFiveLocallyFinite_holds : fourEngelExponentFiveLocallyFinite

/--
Resolved true: Traustason proves that every `4`-Engel `2`-group is locally finite, in particular
every `4`-Engel group with `x⁸ = 1`; the Kourovka Archive answers 9.50(c) "Yes". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.50 (Yu. P. Razmyslov);
resolution: (a) G. Traustason, Two generator 4-Engel groups, Internat. J. Algebra Comput. 15 (2005),
309-316; G. Havas and M. R. Vaughan-Lee, 4-Engel groups are locally nilpotent, Internat. J. Algebra
Comput. 15 (2005), 649-682; A. Abdollahi and G. Traustason, On locally finite p-groups satisfying an
Engel condition, Proc. Amer. Math. Soc. 130 (2002), 2827-2836,
https://doi.org/10.1090/S0002-9939-02-06421-3; (b) M. R. Vaughan-Lee, Engel-4 groups of exponent 5,
Proc. London Math. Soc. (3) 74 (1997), 306-334, https://doi.org/10.1112/S0024611597000117; (c) G.
Traustason, On 4-Engel groups, J. Algebra 178 (1995), 414-429,
https://doi.org/10.1006/jabr.1995.1357, Kourovka Archive of Solved Problems, Problem 9.50: a) Yes;
this follows from the local nilpotency of 4-Engel groups (Traustason; Havas-Vaughan-Lee) and the
affirmative answer for locally nilpotent groups (Abdollahi-Traustason); b) Yes, it is (Vaughan-Lee);
c) Yes; moreover, every 4-Engel 2-group is locally finite (Traustason),
https://doi.org/10.1142/S0218196705002475.
-/
public theorem_wanted fourEngelExponentEightLocallyFinite_holds :
    fourEngelExponentEightLocallyFinite

end MathlibExt.GroupTheory.FourEngelGroupsKourovka9Problem50Wanted
