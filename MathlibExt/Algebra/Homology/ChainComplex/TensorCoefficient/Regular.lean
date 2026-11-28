/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The regular coefficient is the tensor unit

Let R be a commutative ring and K an ℕ-indexed chain complex of R-modules with carrier
universe max(u,v), where R has universe u. The left tensor unitor gives R⊗_R K ≅ K, degreewise
by r⊗x ↦ r·x.

The same chain isomorphism induces the regular-coefficient homology isomorphism in every
degree.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R]
  (K : ChainComplex (ModuleCat.{max u v} R) ℕ)

/-- Let R : Type u be a commutative ring and K a chain complex in ModuleCat.{max(u,v)} R indexed
by ℕ. The regular coefficient R gives a chain isomorphism R⊗_R K ≅ K. Its degree-n component
is the left tensor unitor r⊗x ↦ r·x, with inverse x ↦ 1⊗x. -/
def regularIso : (functor R K).obj (ModuleCat.of R R) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.lid R (K.X n)).toModuleIso)
    (by
      intro i j _h
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro r x
      change (K.d i j).hom (r • x) = r • (K.d i j).hom x
      exact (K.d i j).hom.map_smul r x)

/-- Let R : Type u be a commutative ring, K an ℕ-indexed chain complex in ModuleCat.{max(u,v)} R,
n ∈ ℕ, r ∈ R, and x ∈ K_n. The degree-n forward map of regularIso sends r⊗x to r·x. -/
theorem regularIso_tmul (n : ℕ) (r : R) (x : K.X n) :
    ((regularIso R K).hom.f n).hom (r ⊗ₜ[R] x) = r • x :=
  TensorProduct.lid_tmul x r

/-- Let R be a commutative ring and K an ℕ-indexed R-module chain complex with carrier universe
max(u,v). For every n ∈ ℕ, the chain unitor R⊗_R K ≅ K induces H_n(R⊗_R K) ≅ H_n(K). No
flatness hypothesis on the terms is needed. -/
def regularHomologyIso (n : ℕ) :
    ((functor R K).obj (ModuleCat.of R R)).homology n ≅ K.homology n :=
  HomologicalComplex.homologyMapIso (regularIso R K) n

end ChainComplex.TensorCoefficient
