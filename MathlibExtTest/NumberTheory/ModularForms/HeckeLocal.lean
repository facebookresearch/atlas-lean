/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeLocal

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    [Fact (CuspForm.HasIntegralStructure N 2)] (t : ↥(CuspForm.heckeAlgebra N 2 S)) :
    IsLocalRing.residue (CuspForm.heckeLocal N S 𝒪 θ) (CuspForm.heckeLocal.π N S 𝒪 θ t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) (θ t) :=
  CuspForm.heckeLocal.residue_pi N S 𝒪 θ t

/-- Higher-universe consumer: the coefficient ring may live in any universe. -/
example (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type 1) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    [Fact (CuspForm.HasIntegralStructure N 2)] (t : ↥(CuspForm.heckeAlgebra N 2 S)) :
    IsLocalRing.residue (CuspForm.heckeLocal N S 𝒪 θ) (CuspForm.heckeLocal.π N S 𝒪 θ t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) (θ t) :=
  CuspForm.heckeLocal.residue_pi N S 𝒪 θ t

/-- Under an integral structure and completeness of `𝒪`, the local Hecke algebra is a
complete local ring, finite and free over `𝒪`. -/
example (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    [Fact (CuspForm.HasIntegralStructure N 2)] :
    IsLocalRing (CuspForm.heckeLocal N S 𝒪 θ) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (CuspForm.heckeLocal N S 𝒪 θ))
        (CuspForm.heckeLocal N S 𝒪 θ) ∧
      Module.Finite 𝒪 (CuspForm.heckeLocal N S 𝒪 θ) ∧
      Module.Free 𝒪 (CuspForm.heckeLocal N S 𝒪 θ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
