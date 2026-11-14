/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public noncomputable section

/-!
# Native continuous adic compact-support/finite-level comparison

Authors: Bhargav Bhatt, Peter Scholze.
Source: The pro-étale topology for schemes, §6.8,
https://arxiv.org/abs/1309.1198; Stacks Tags 03UT, 09AH and 09BT.

The displayed kernel and comparison are actual small pro-étale objects,
units and coefficient maps. Existing Axiom torsion/adic compact supports,
open-closed exactness and generic derived completion are toolbox; this
goal identifies the native continuous compact-support coefficient model
with its prescribed finite-level classes. It does not request a new trace
formula or a generic inverse-limit theorem.
-/

namespace WantedExt.AlgebraicGeometry.ContinuousAdicCompactSupports

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

universe u

/-- The canonical native compact-support reduction comparison is bijective
for a finite-type scheme over an algebraically closed field, with ell invertible. -/
public theorem_wanted compactSupportLimitComparison_bijective
    (ell : ℕ) [Fact ell.Prime] [ReductionMaps ell]
    (k : Type u) [Field k] [IsAlgClosed k] (ellInvertible : (ell : k) ≠ 0)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (c : ClosedCompactification X) (n : ℕ) :
    Function.Bijective (compactSupportLimitComparison ell c n)

end WantedExt.AlgebraicGeometry.ContinuousAdicCompactSupports
