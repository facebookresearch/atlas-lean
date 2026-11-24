/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.DualHochschildForms

/-!
# The generator-normalized native-form/dual-Hochschild comparison

Hochschild--Kostant--Rosenberg, *Differential forms on regular affine
algebras*, Trans. AMS102(1962)383–408; Loday, *Cyclic Homology*, §3.4.
The map is fixed by 1/n!·ψ(a0 da1∧…∧dan), with actual Kähler/exterior
modules and the actual existing cocycle/cohomology maps. Smoothness is
the native Algebra.Smooth predicate of the specified affine algebra.
No cohomology comparison, dg/CY predicate or isomorphism is assumed.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DualHochschildFormsWanted

open MathlibExt.RingTheory.DualHochschildForms

universe u

/-- Native smooth affine forms compute the existing dual-coefficient Hochschild cohomology,
through the exact displayed HKR cochain formula. -/
public theorem_wanted smooth_dual_hkr (k A : Type u) [Field k] [CharZero k]
    [CommRing A] [Algebra k A] [_root_.Algebra.Smooth k A] (n : ℕ) :
    ∃ h : ∀ ψ : Forms k A n →ₗ[k] k,
      hkrCochain k A n ψ ∈ TauCeti.hochschildCocycles k A k n,
      Function.Bijective (hkrOnCohomology k A n h)

end WantedExt.AlgebraicGeometry.DualHochschildFormsWanted
