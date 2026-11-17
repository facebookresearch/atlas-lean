/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Actual completed tensor factors for finite-extension adelic norms

The coefficient algebra is the complete tensor `E ⊗[K] F`, including its
nilpotents. A factorization is an algebra isomorphism with finite local
Artinian algebras. The residue field of each factor is its literal
maximal-ideal quotient. Its composition length and residue/completion
field rank are computed separately; their product is the metric exponent.

The residue field alone does not replace the Artinian factor. No
separability assumption occurs. This includes inseparable finite extensions
in the function-field case. Comparison with actual place completions
retains the original `E` map and the original completed-base scalar map.

References: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1;
the finite-algebra length/norm decomposition used for the relative-dimension
zero Deligne pairing. Native primitives are Mathlib `Module.length`,
`IsLocalRing.ResidueField`, `Algebra.norm`, and the tensor algebra.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual base-changed field algebra; it need not be reduced. -/
abbrev CompletedTensor (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] := E ⊗[K] F

/-- A full local-Artinian decomposition of that same tensor algebra. -/
structure Factorization (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E] where
  index : Type
  [finiteIndex : Fintype index]
  factor : index → Type
  [ring : ∀ i, CommRing (factor i)]
  [nontrivial : ∀ i, Nontrivial (factor i)]
  [localRing : ∀ i, IsLocalRing (factor i)]
  [artinian : ∀ i, IsArtinianRing (factor i)]
  [noetherian : ∀ i, IsNoetherianRing (factor i)]
  [algebra : ∀ i, Algebra F (factor i)]
  [finite : ∀ i, FiniteDimensional F (factor i)]
  decomposition : CompletedTensor K E F ≃ₐ[F] (∀ i, factor i)

attribute [instance] Factorization.finiteIndex Factorization.ring
  Factorization.nontrivial Factorization.localRing Factorization.artinian
  Factorization.noetherian Factorization.algebra Factorization.finite

variable {K E F : Type} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [FiniteDimensional K E]
  (D : Factorization K E F)

/-- The actual residue field of this local tensor factor. -/
abbrev Residue (i : D.index) := IsLocalRing.ResidueField (D.factor i)

/-- The original `E` scalar, projected through the full tensor factor. -/
def factorMap (i : D.index) : E →+* D.factor i :=
  (Pi.evalRingHom D.factor i).comp
    (D.decomposition.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft : E →ₐ[K] CompletedTensor K E F).toRingHom)

/-- The actual quotient map, not a chosen embedding into an unrelated field. -/
def residueMap (i : D.index) : E →+* Residue D i :=
  (IsLocalRing.residue (D.factor i)).comp (factorMap D i)

/-- Finite local composition length counts nilpotent multiplicity. -/
def factorLength (i : D.index) : ℕ :=
  (Module.length (D.factor i) (D.factor i)).toNat

/-- The independent rank of the actual residue field over the completed base. -/
def residueRank (i : D.index) : ℕ := Module.finrank F (Residue D i)

/-- The full local metric exponent includes both length and field rank. -/
def metricWeight (i : D.index) : ℕ := factorLength D i * residueRank D i

def totalWeight : ℕ := ∑ i : D.index, metricWeight D i

/-- Field norms are computed in the genuine residue field, with Artinian length. -/
def factorNorm (a : E) : F :=
  ∏ i : D.index, Algebra.norm F (residueMap D i a) ^ factorLength D i

@[simp] theorem residueMap_one (i : D.index) : residueMap D i 1 = 1 := map_one _

@[simp] theorem factorNorm_one : factorNorm D 1 = 1 := by
  simp [factorNorm]

end MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors

namespace MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {K E F : Type} [Field K] [Field E] [NormedField F] [CompleteSpace F]
  [Algebra K E] [Algebra K F] [FiniteDimensional K E]
  (D : Factorization K E F)

/-- Actual complete field realizations of the tensor residue factors.
Their base scalars are isometric, and the comparison is an `F`-algebra
equivalence. It therefore fixes the completed-base coefficient action. -/
structure CompletionData where
  completion : D.index → Type
  [normed : ∀ i, NormedField (completion i)]
  [complete : ∀ i, CompleteSpace (completion i)]
  [algebra : ∀ i, Algebra F (completion i)]
  [finite : ∀ i, FiniteDimensional F (completion i)]
  comparison : ∀ i, Residue D i ≃ₐ[F] completion i
  scalar_isometry : ∀ (i : D.index) (a : F), ‖algebraMap F (completion i) a‖ = ‖a‖

attribute [instance] CompletionData.normed CompletionData.complete
  CompletionData.algebra CompletionData.finite

variable (C : CompletionData D)

/-- The `E` map in this completion is fixed by the actual tensor/residue map. -/
def completionMap (i : D.index) : E →+* C.completion i :=
  (C.comparison i).toRingEquiv.toRingHom.comp (residueMap D i)

/-- Rank of the actual complete extension field, rather than a global degree. -/
def completionRank (i : D.index) : ℕ := Module.finrank F (C.completion i)

def completionWeight (i : D.index) : ℕ := factorLength D i * completionRank D C i

/-- The normalized local norm expression retains every factor and multiplicity. -/
def completedNorm (a : E) : ℝ :=
  ∏ i : D.index, ‖completionMap D C i a‖ ^ completionWeight D C i

@[simp] theorem completedNorm_one : completedNorm D C 1 = 1 := by
  simp [completedNorm, completionMap]

end MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors
