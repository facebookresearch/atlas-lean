/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PatchingDatum

@[expose] public section

/-- The level projection of a patching datum has the expected type, and its
surjectivity data is accessible. -/
example {𝒪 : Type} [CommRing 𝒪] {ℓ r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] (D : Algebra.PatchingDatum 𝒪 ℓ r R M)
    (n : ℕ) :
    Function.Surjective ((D.level n).π) :=
  (D.level n).π_surjective

section

variable {𝒪 : Type} [CommRing 𝒪] {ℓ r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] (D : Algebra.PatchingDatum 𝒪 ℓ r R M)
    (n : ℕ)

-- The published instances must synthesize through the dependent level projection.
example : AddCommGroup (D.level n).N := inferInstance

example : Module (MvPowerSeries (Fin r) 𝒪) (D.level n).N := inferInstance

end
