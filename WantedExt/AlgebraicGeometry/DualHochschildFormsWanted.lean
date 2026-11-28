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

/-- **Dual Hochschild–Kostant–Rosenberg theorem for smooth algebras.** Let $k$ be a field of
characteristic zero, $A$ a smooth commutative $k$-algebra and $n \in \mathbb{N}$. For every
$k$-linear form $\psi$ on $\Omega^n_{A/k}$, the cochain
$(a_0, \dots, a_n) \mapsto \frac{1}{n!}\,\psi(a_0\, da_1 \wedge \dots \wedge da_n)$ is a Hochschild
cocycle ($k$-valued cochains in $n + 1$ arguments, that is, coefficients in the dual bimodule
$A^*$), and the induced map $\mathrm{Hom}_k(\Omega^n_{A/k}, k) \to HH^n(A, A^*)$ is bijective. -/
public theorem_wanted smooth_dual_hkr (k A : Type u) [Field k] [CharZero k]
    [CommRing A] [Algebra k A] [_root_.Algebra.Smooth k A] (n : ℕ) :
    ∃ h : ∀ ψ : Forms k A n →ₗ[k] k,
      hkrCochain k A n ψ ∈ TauCeti.hochschildCocycles k A k n,
      Function.Bijective (hkrOnCohomology k A n h)

end WantedExt.AlgebraicGeometry.DualHochschildFormsWanted
