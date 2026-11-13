/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The congruence kernel of SL₂(ℤ) is free profinite (Kourovka Notebook Problem 3.40)

Kourovka Notebook, Archive of Solved Problems, Problem 3.40 (I. R. Shafarevich; V. P. Platonov): let
`SL₂(ℤ)^` and `SL₂(ℤ)^-` denote the completions of `SL₂(ℤ)` determined by all subgroups of finite
index and all congruence subgroups, respectively, and let `ψ : SL₂(ℤ)^ → SL₂(ℤ)^-` be the natural
homomorphism. Is `Ker ψ` a free profinite group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

@[expose] public section

namespace MathlibExt.GroupTheory.CongruenceKernelFreeProfiniteKourovka3Problem40Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.40 (I. R.
Shafarevich; V. P. Platonov). UnsolvedMath record UM-00700189 (`KOU-3.40`), dataset
ulamai/UnsolvedMath v1.8.0.

`SL₂(ℤ)^` is Mathlib's profinite completion `ProfiniteGrp.ProfiniteCompletion.completion` (the limit
of the quotients by normal subgroups of finite index, with the projections of
`ProfiniteGrp.limitCone`). The principal congruence subgroups `Γ(n)` are cofinal among the
congruence subgroups, so `Ker ψ` consists of the elements with trivial image in every `SL₂(ℤ) /
Γ(n)`. Free profinite groups are not in Mathlib; freeness is stated by the universal property on a
family `ι : X → K` converging to `1`, tested against finite groups, which suffices for a profinite
`K` (a closed subgroup of the profinite completion).
-/

open CategoryTheory

/-- The principal congruence subgroup `Γ(n + 1)` of `SL₂(ℤ)` (the kernel of reduction modulo
`n + 1`), as a normal subgroup of finite index. -/
def principalCongruenceSubgroup (n : ℕ) :
    FiniteIndexNormalSubgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) where
  toSubgroup := CongruenceSubgroup.Gamma (n + 1)
  isNormal' := CongruenceSubgroup.Gamma_normal _

/-- The profinite completion `SL₂(ℤ)^`: Mathlib's `ProfiniteGrp.ProfiniteCompletion.completion`,
the limit of the finite quotients `SL₂(ℤ) / N` over the normal subgroups `N` of finite index. -/
noncomputable abbrev profiniteCompletionSL2 : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) ℤ))

/-- The kernel of the natural map `ψ : SL₂(ℤ)^ → SL₂(ℤ)^-` onto the congruence completion: the
elements whose image in `SL₂(ℤ) / Γ(n + 1)` (under the projection of the limit cone
`ProfiniteGrp.limitCone` that defines the completion) is trivial for every `n`, since the
principal congruence subgroups are cofinal among the congruence subgroups. -/
noncomputable def congruenceKernel : Subgroup profiniteCompletionSL2 :=
  ⨅ n : ℕ, MonoidHom.ker ((ProfiniteGrp.limitCone (ProfiniteGrp.ProfiniteCompletion.diagram
    (GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) ℤ)))).π.app
      (principalCongruenceSubgroup n)).hom.toMonoidHom

/-- Kourovka 3.40 (I. R. Shafarevich; V. P. Platonov): the kernel `K` of the natural homomorphism
from the profinite completion of `SL₂(ℤ)` onto its congruence completion is a free profinite group:
it has a family `ι : X → K` converging to `1` (outside each open neighbourhood of `1` lie only
finitely many `ι x`) such that every map `f : X → Q` into a finite group with `f x = 1` for almost
all `x` extends uniquely to a continuous homomorphism `K → Q` (one with open kernel). For the
profinite group `K`, testing finite groups `Q` suffices. -/
def congruenceKernelFreeProfinite : Prop :=
  ∃ (X : Type) (ι : X → congruenceKernel),
    (∀ U : Set congruenceKernel, IsOpen U → 1 ∈ U → {x | ι x ∉ U}.Finite) ∧
    ∀ (Q : Type) [Group Q] [Finite Q] (f : X → Q), {x | f x ≠ 1}.Finite →
      ∃! φ : congruenceKernel →* Q, IsOpen (φ.ker : Set congruenceKernel) ∧ ∀ x, φ (ι x) = f x

/--
Resolved true: the Kourovka Archive answers 3.40 "Yes, it is", citing Mel'nikov (Soviet Math. Dokl.
17 (1976)): the kernel of the natural map from the profinite completion of `SL₂(ℤ)` to its
congruence completion is a free profinite group. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 3.40 (I. R. Shafarevich; V. P. Platonov); resolution: O. V.
Mel'nikov, Soviet Math. Dokl. 17 (1976), 867-870, Kourovka Archive, Problem 3.40: Yes, it is,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted congruenceKernelFreeProfinite_holds : congruenceKernelFreeProfinite

end MathlibExt.GroupTheory.CongruenceKernelFreeProfiniteKourovka3Problem40Wanted
