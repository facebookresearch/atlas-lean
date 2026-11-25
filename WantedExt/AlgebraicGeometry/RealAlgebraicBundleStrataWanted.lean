/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata

/-!
# Uniform nonsingular strata for stratified-algebraic real bundles

Kucharz--Kurdyka, *Stratified-algebraic vector bundles*, arXiv:1308.4376v1,
Theorem 1.5 (for real vector bundles): any compact real algebraic variety `X`
admits a nonsingular stratification `S` such that each stratified-algebraic
vector bundle on `X` is isomorphic, *in the category of stratified-algebraic
vector bundles on `X`*, to an `S`-algebraic vector bundle. By the paper's
Definition 1.2, a morphism in that category is a `T`-algebraic morphism for
some stratification `T` on which both bundles are `T`-algebraic; this is
`IsAlgebraicIsoFor a R` below, where `R` may be taken to refine the input and
output stratifications (common refinements preserve algebraicity). The single
stratification `S` works for every stratified-algebraic bundle; the theorem
is not asserted for every topological vector bundle.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RealAlgebraicBundleStrataWanted

open MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata

/-- Kucharz--Kurdyka, Theorem 1.5: a uniform nonsingular stratification for all
stratified-algebraic real vector bundles on a compact real algebraic variety. -/
def_wanted uniform_bundle_stratification (n : ℕ) (X : RealVariety n)
    (hcompact : IsCompact X.locus) :
    {S : Stratification X // S.nonsingular ∧
      ∀ (r : ℕ) (P : ProjectionBundle X r) (SP : Stratification X), IsAlgebraicFor P SP →
        ∃ (s : ℕ) (Q : ProjectionBundle X s) (a : BundleIso P Q) (R : Stratification X),
          IsAlgebraicFor Q S ∧ Refines R SP ∧ Refines R S ∧ IsAlgebraicIsoFor a R}

end WantedExt.AlgebraicGeometry.RealAlgebraicBundleStrataWanted
