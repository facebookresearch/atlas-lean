/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-index subgroups of Out(F_n), n ≥ 5, have finite abelianization (AIM Out(F_n), 3.2)

AIM workshop The geometry of the outer automorphism group of a free group, problem list, Problem
3.2: does there exist a finite index subgroup `Γ < Out(Fₙ)` with infinite abelianization? (Context,
Problem 3.1: does `Out(Fₙ)` have Property (T) or (τ) if `n ≥ 4`? `Out(F₃)` does not have Property
(T) because it has a finite index subgroup `Γ` with `|H₁(Γ, ℤ)| = ∞`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.OutFreeGroupAbelianizationAIMGeometricGroupTheoryProblem153Wanted

/-!
Source: AIM workshop The geometry of the outer automorphism group of a free group, problem list,
https://aimath.org/WWN/outerauto/outerauto.pdf, Problem 3.2 (with Problem 3.1). UnsolvedMath record
UM-20001644 (`AIM-GEOMETRIC_GROUP_THEORY-0153`), dataset ulamai/UnsolvedMath v1.8.0.

`Out(Fₙ) = Aut(Fₙ) / Inn(Fₙ)`, with `Inn(Fₙ)` the normal closure of the image of `MulAut.conj` (that
image itself). Only `n ≥ 5` is formalized, where the answer is no: `Out(Fₙ)` has Property (T)
(Kaluba-Kielak-Nowak for `n ≥ 6`, Kaluba-Nowak-Ozawa for `n = 5`), Property (T) passes to
finite-index subgroups, and a countable group with Property (T) has finite abelianization, each step
as printed in the sources quoted in the theorem's docstring. For `n = 2, 3` the answer is yes (the
list's `Out(F₃)` remark), and `n = 4` would rest on Nitsche's computer-assisted proof of Property
(T) for `Aut(F₄)` (arXiv:2009.05134; no journal publication found), so it is omitted.
-/

/-- The inner automorphisms of the free group `Fₙ`, as a normal subgroup of `Aut(Fₙ)` (the normal
closure of the image of `MulAut.conj`, which is that image itself). -/
abbrev innerAutFree (n : ℕ) : Subgroup (MulAut (FreeGroup (Fin n))) :=
  Subgroup.normalClosure (Set.range (MulAut.conj : FreeGroup (Fin n) →* MulAut (FreeGroup (Fin n))))

/-- The outer automorphism group `Out(Fₙ) = Aut(Fₙ) / Inn(Fₙ)`. -/
abbrev OutFree (n : ℕ) : Type := MulAut (FreeGroup (Fin n)) ⧸ innerAutFree n

/-- The AIM question (The geometry of the outer automorphism group of a free group, Problem 3.2) for
some `n ≥ 5`: `Out(Fₙ)` has a finite-index subgroup with infinite abelianization. -/
def outFreeVirtuallyInfiniteAbelianization : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ ∃ H : Subgroup (OutFree n), H.FiniteIndex ∧ Infinite (Abelianization H)

/--
Resolved false for every `n ≥ 5`. `Out(Fₙ)` has Property (T): Kaluba-Kielak-Nowak, Theorem 5.9: "For
every n ≥ 6, the groups SAut(Fn), Aut(Fn) and Out(Fn) have Kazhdan's property (T)", and
Kaluba-Nowak-Ozawa, Corollary 2: "The groups Aut(F5) and Out(F5) have property (T)". Every
finite-index subgroup of `Out(Fₙ)` then has Property (T): Bridson and Vogtmann note that "property
(T) passes to finite-index subgroups" (Farb (ed.), Problems on Mapping Class Groups and Related
Topics, Chapter 20, Section 2.2, PDF p. 330), and Bekka, de la Harpe and Valette state that "a
lattice in a locally compact group G has Property (T) if and only if G has Property (T)" (Kazhdan's
Property (T), Introduction, p. 5). The same page states that "a countable group Γ with Property (T)
is finitely generated and its first homology group H1(Γ, Z) = Γ/[Γ, Γ] is finite", so every
finite-index subgroup of `Out(Fₙ)`, `n ≥ 5`, has finite abelianization. Source: AIM workshop The
geometry of the outer automorphism group of a free group, problem list,
https://aimath.org/WWN/outerauto/outerauto.pdf, Problem 3.2 (with Problem 3.1); resolution: M.
Kaluba, D. Kielak and P. W. Nowak, On property (T) for Aut(F_n) and SL_n(Z), Ann. of Math. (2) 193
(2021), 539-562, Theorem 5.9, https://doi.org/10.4007/annals.2021.193.2.3; M. Kaluba, P. W. Nowak
and N. Ozawa, Aut(F_5) has property (T), Math. Ann. 375 (2019), 1169-1191, Corollary 2,
https://arxiv.org/abs/1712.07167; B. Bekka, P. de la Harpe and A. Valette, Kazhdan's Property (T),
Cambridge University Press (2008), Introduction, p. 5,
https://assets.cambridge.org/97805218/87205/excerpt/9780521887205_excerpt.pdf.
-/
public theorem_wanted outFreeVirtuallyInfiniteAbelianization_refuted :
    ¬ outFreeVirtuallyInfiniteAbelianization

end MathlibExt.GroupTheory.OutFreeGroupAbelianizationAIMGeometricGroupTheoryProblem153Wanted
