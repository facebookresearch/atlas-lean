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
# Regular coefficients in the chain tensor functor

The left tensor unitor identifies tensoring a chain complex with the
regular coefficient ring with the chain complex itself, preserving
components and differentials.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R]
  (K : ChainComplex (ModuleCat.{max u v} R) ℕ)

/-- The regular coefficient has the original complex as its actual tensor-unit target. -/
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

/-- The original regular tensor class maps to its actual scalar action. -/
theorem regularIso_tmul (n : ℕ) (r : R) (x : K.X n) :
    ((regularIso R K).hom.f n).hom (r ⊗ₜ[R] x) = r • x :=
  TensorProduct.lid_tmul x r

/-- The same native chain unitor computes the actual regular-coefficient homology. -/
def regularHomologyIso (n : ℕ) :
    ((functor R K).obj (ModuleCat.of R R)).homology n ≅ K.homology n :=
  HomologicalComplex.homologyMapIso (regularIso R K) n

end ChainComplex.TensorCoefficient
