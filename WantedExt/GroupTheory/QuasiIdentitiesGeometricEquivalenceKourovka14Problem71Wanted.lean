/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quasi-identities and geometric equivalence of groups (Kourovka Notebook Problem 14.71)

Kourovka Notebook, Archive of Solved Problems, Problem 14.71 (B. I. Plotkin): groups `G` and `H` are
geometrically equivalent if `cl_G(T) = cl_H(T)` for every free group `F` of finite rank and every `T
⊆ F`, where `cl_G(T)` is the intersection of the kernels of all homomorphisms `F → G` vanishing on
`T`. If two groups have the same quasi-identities, are they geometrically equivalent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.71 (B. I.
Plotkin). UnsolvedMath record UM-00701056 (`KOU-14.71`), dataset ulamai/UnsolvedMath v1.8.0.

Homomorphisms `F_n → G` are given by the images of the basis; `T` ranges over all subsets (possibly
infinite), which is where the two notions can differ. Quasi-identities are `∀ x (w₁ = 1 ∧ ⋯ ∧ wₖ = 1
→ w = 1)` with finitely many premises.
-/

/-- A quasi-identity `∀ x (w₁ = 1 ∧ ⋯ ∧ wₖ = 1 → w = 1)` in the unknowns `x₀, …, xₙ₋₁`. -/
structure QuasiIdentity where
  /-- The number of unknowns. -/
  n : ℕ
  /-- The premises `w₁, …, wₖ`. -/
  premises : List (FreeGroup (Fin n))
  /-- The conclusion `w`. -/
  conclusion : FreeGroup (Fin n)

/-- The quasi-identity `q` holds in the group `G`. -/
def QuasiIdentity.HoldsIn (q : QuasiIdentity) (G : Type*) [Group G] : Prop :=
  ∀ x : Fin q.n → G, (∀ w ∈ q.premises, FreeGroup.lift x w = 1) →
    FreeGroup.lift x q.conclusion = 1

/-- The `G`-closure `cl_G(T)` of `T ⊆ F_n`: the intersection of the kernels of all homomorphisms
`μ : F_n → G` (given by the images `x` of the basis) that vanish on `T`. -/
def gClosure (G : Type*) [Group G] {n : ℕ} (T : Set (FreeGroup (Fin n))) :
    Set (FreeGroup (Fin n)) :=
  {w | ∀ x : Fin n → G, (∀ t ∈ T, FreeGroup.lift x t = 1) → FreeGroup.lift x w = 1}

/-- `G` and `H` are geometrically equivalent (B. I. Plotkin): `cl_G(T) = cl_H(T)` for every free
group `F_n` of finite rank and every `T ⊆ F_n`. -/
def GeometricallyEquivalent (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ (n : ℕ) (T : Set (FreeGroup (Fin n))), gClosure G T = gClosure H T

/-- Kourovka 14.71 (B. I. Plotkin): two groups satisfying the same quasi-identities are
geometrically equivalent. -/
def sameQuasiIdentitiesImpliesGeometricallyEquivalent : Prop :=
  ∀ (G H : Type) [Group G] [Group H], (∀ q : QuasiIdentity, q.HoldsIn G ↔ q.HoldsIn H) →
    GeometricallyEquivalent G H

/--
Resolved false: the Kourovka Archive answers 14.71 "No, not always", citing Bludov, Göbel and
Shelah, and Myasnikov and Remeslennikov: some groups with the same quasi-identities are not
geometrically equivalent. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.71 (B. I. Plotkin); resolution: V. V. Bludov, Abstracts of the 7th Int. Conf. Groups and
Group Rings, Supraśl, 1999, p. 6; R. Göbel and S. Shelah, Proc. Amer. Math. Soc. 130 (2002),
673-674; A. G. Myasnikov and V. N. Remeslennikov, J. Algebra 234 (2000), no. 1, 225-276, Kourovka
Archive, Problem 14.71 (answer: No, not always).
-/
public theorem_wanted sameQuasiIdentitiesImpliesGeometricallyEquivalent_refuted :
    ¬ sameQuasiIdentitiesImpliesGeometricallyEquivalent

end MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted
