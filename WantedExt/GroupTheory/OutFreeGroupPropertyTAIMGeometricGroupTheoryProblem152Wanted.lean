/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Out(F_n) has Kazhdan's property (T) for n ≥ 5 (AIM outer automorphism list, Problem 3.1)

The geometry of the outer automorphism group of a free group (AIM problem list, ed. J. Mangahas),
Problem 3.1: does `Out(F_n)` have property (T) or (τ) if `n ≥ 4`? (`Out(F₃)` does not have property
(T).) For `n ≥ 5` the answer is yes: `Out(F_n)` has property (T), which implies (τ).
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.OnPropertyTWanted
public import WantedExt.GroupTheory.OutFreeGroupAbelianizationAIMGeometricGroupTheoryProblem153Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.OutFreeGroupPropertyTAIMGeometricGroupTheoryProblem152Wanted

/-!
Source: The geometry of the outer automorphism group of a free group, AIM workshop problem list (ed.
J. Mangahas), Problem 3.1, https://aimath.org/WWN/outerauto/outerauto.pdf. UnsolvedMath record
UM-20001643 (`AIM-GEOMETRIC_GROUP_THEORY-0152`), dataset ulamai/UnsolvedMath v1.8.0.

`Out(F_n)` is `OutFree n` of `OutFreeGroupAbelianizationAIMGeometricGroupTheoryProblem153Wanted`:
`MulAut (FreeGroup (Fin n))` modulo the normal closure of the inner automorphisms (which is the
subgroup of inner automorphisms). Property (T) is the predicate `PropertyT` of `OnPropertyTWanted`,
the definition of Kaluba-Kielak-Nowak (their equation (2), due to Ozawa): a finite symmetric
generating set `S` and `λ > 0` such that `Δ² - λΔ` is a sum of hermitian squares in `ℝG`, where
`Δ = |S| - ∑_{s ∈ S} s`. For finitely generated groups such as `Out(F_n)` this is Kazhdan's
property (T) (Ozawa's characterization), and Kaluba-Kielak-Nowak note that it does not depend on
the generating set. The same predicate states property (T) of `Aut(F_n)` in
`AutFreeGroupPropertyTAMR109Problem0272Wanted`. The case `n = 4` rests only on an unrefereed
computer-assisted preprint (Nitsche, arXiv:2009.05134, for `Aut(F₄)`) and is the OpenConjectures
entry AIMGeometricGroupTheoryProblem152.
-/

open MathlibExt.GroupTheory.OnPropertyTWanted.OnPropertyT (PropertyT)
open MathlibExt.GroupTheory.OutFreeGroupAbelianizationAIMGeometricGroupTheoryProblem153Wanted
  (OutFree)

/-- The outer automorphism group `Out(F_n)` (`OutFree n`) has Kazhdan's property (T) (`PropertyT`,
the Ozawa characterization used by Kaluba-Kielak-Nowak) for every `n ≥ 5`. -/
def outFreeGroupHasPropertyT : Prop :=
  ∀ n : ℕ, 5 ≤ n → PropertyT (OutFree n)

/--
Resolved true: `Out(F_n)` has Kazhdan's property (T) for every `n ≥ 5`. Kaluba-Kielak-Nowak, Theorem
5.9: 'For every n ⩾ 6, the groups SAut(F_n), Aut(F_n) and Out(F_n) have Kazhdan's property (T)',
with property (T) defined by their equation (2) (the predicate `PropertyT`); Kaluba-Nowak-Ozawa,
Corollary 2: 'The groups Aut(F₅) and Out(F₅) have property (T)'. Property (T) implies property (τ).
Source: The geometry of the outer automorphism group of a free group, AIM workshop problem list (ed.
J. Mangahas), Problem 3.1, https://aimath.org/WWN/outerauto/outerauto.pdf; resolution: M. Kaluba,
D. Kielak and P. W. Nowak, On property (T) for Aut(F_n) and SL_n(Z), Ann. of Math. 193 (2021), no.
2, 539-562, arXiv:1812.03456, Theorem 5.9 and equation (2) (n ≥ 6); M. Kaluba, P. W. Nowak and N.
Ozawa, Aut(F_5) has property (T), Math. Ann. 375 (2019), 1169-1191, arXiv:1712.07167, Corollary 2
(n = 5), https://doi.org/10.4007/annals.2021.193.2.3.
-/
public theorem_wanted outFreeGroupHasPropertyT_holds : outFreeGroupHasPropertyT

end MathlibExt.GroupTheory.OutFreeGroupPropertyTAIMGeometricGroupTheoryProblem152Wanted
