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

Kucharz--Kurdyka, 1308.4376v1, Theorem 1.5. The single stratification works
for every specified stratified-algebraic bundle. The isomorphism and its
inverse are regular on a common refinement of the input and output strata;
the theorem is not asserted for every topological vector bundle.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata

def_wanted uniform_bundle_stratification (n : ℕ) (X : RealVariety n)
    (hcompact : IsCompact X.locus) :
    {S : Stratification X // S.nonsingular ∧
      ∀ (r : ℕ) (P : ProjectionBundle X r) (SP : Stratification X), IsAlgebraicFor P SP →
        ∃ (s : ℕ) (Q : ProjectionBundle X s) (a : BundleIso P Q) (R : Stratification X),
          IsAlgebraicFor Q S ∧ Refines R SP ∧ Refines R S ∧ IsAlgebraicIsoFor a R}

end MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata

