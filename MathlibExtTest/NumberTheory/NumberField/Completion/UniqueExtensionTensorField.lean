/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.UniqueExtensionTensorField

@[expose] public section

open scoped TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open NumberField IsDedekindDomain

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- Consumer with the original binders, with extensions recorded as places
lying over the base place. -/
example (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] (v : HeightOneSpectrum (𝓞 F))
    (hA : IsField (M ⊗[F] v.adicCompletion F)) :
    ∃ (w : v.placesOver M)
      (e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F]
        w.val.adicCompletion M),
      (∀ w' : v.placesOver M, w' = w) ∧
      (∀ x : M, e (x ⊗ₜ[F] 1) = algebraMap M (w.val.adicCompletion M) x) ∧
      Module.finrank (v.adicCompletion F) (w.val.adicCompletion M) =
        Module.finrank F M :=
  v.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor hA

/-- Higher-universe consumer. -/
example (F M : Type (u + 1)) [Field F] [NumberField F] [Field M]
    [NumberField M] [Algebra F M] (v : HeightOneSpectrum (𝓞 F))
    (hA : IsField (M ⊗[F] v.adicCompletion F)) :
    ∃ (w : v.placesOver M)
      (e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F]
        w.val.adicCompletion M),
      (∀ w' : v.placesOver M, w' = w) ∧
      (∀ x : M, e (x ⊗ₜ[F] 1) = algebraMap M (w.val.adicCompletion M) x) ∧
      Module.finrank (v.adicCompletion F) (w.val.adicCompletion M) =
        Module.finrank F M :=
  v.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor hA

/-- Boundary: a product of two fields is not a field, so the field
hypothesis on the tensor product cannot be dropped when there are two
distinct extensions. -/
example : ¬ IsField (ℚ × ℚ) := by
  intro h
  letI := h.toField
  have h1 : ((1, 0) : ℚ × ℚ) ≠ 0 := by simp
  have h2 : ((0, 1) : ℚ × ℚ) ≠ 0 := by simp
  exact (mul_ne_zero h1 h2) (by ext <;> simp)
