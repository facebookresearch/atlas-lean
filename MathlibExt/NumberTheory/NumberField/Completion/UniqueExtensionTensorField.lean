/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_
algEquiv_adicCompletion_of_isField_tensor.lean`,
`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_
algEquiv_of_baseChange.lean`
and
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_
algEquiv_adicCompletion_of_isField_tensor.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductEquiv
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open scoped TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace IsDedekindDomain.HeightOneSpectrum

open NumberField

private theorem nonempty_and_subsingleton_of_isField_pi {ι : Type*}
    (K : ι → Type*) [∀ i, Field (K i)] (h : IsField (∀ i, K i)) :
    Nonempty ι ∧ ∀ i j : ι, i = j := by
  classical
  constructor
  · by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  · intro i j
    by_contra hij
    letI := h.toField
    have hx : (Pi.single i (1 : K i) : ∀ k, K k) ≠ 0 := by
      intro h0
      have := congr_fun h0 i
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have hy : (Pi.single j (1 : K j) : ∀ k, K k) ≠ 0 := by
      intro h0
      have := congr_fun h0 j
      rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    have hprod : (Pi.single i (1 : K i) : ∀ k, K k) *
        Pi.single j (1 : K j) = 0 := by
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_of_ne hij, mul_zero]
      · rw [Pi.single_eq_of_ne hk, zero_mul]
    exact (mul_ne_zero hx hy) hprod

/-- If `M ⊗[F] F_v` is a field, then `v` has a unique extension to `M`, and
the tensor product is the completion of `M` at that extension.

Here an extension of `v` is recorded as a place of `M` lying over `v`, the
Mathlib-style form of the extension type in the source statement. -/
public theorem exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
    {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] (v : HeightOneSpectrum (𝓞 F))
    (hA : IsField (M ⊗[F] v.adicCompletion F)) :
    ∃ (w : v.placesOver M)
      (e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F]
        w.val.adicCompletion M),
      (∀ w' : v.placesOver M, w' = w) ∧
      (∀ x : M, e (x ⊗ₜ[F] 1) = algebraMap M (w.val.adicCompletion M) x) ∧
      Module.finrank (v.adicCompletion F) (w.val.adicCompletion M) =
        Module.finrank F M := by
  classical
  have hF : IsField (∀ w : v.placesOver M, w.val.adicCompletion M) :=
    MulEquiv.isField hA
      (completionTensorProductRightAlgEquiv v).symm.toMulEquiv
  obtain ⟨⟨w⟩, huniq⟩ := nonempty_and_subsingleton_of_isField_pi
    (fun w : v.placesOver M => w.val.adicCompletion M) hF
  let e₀ : M ⊗[F] v.adicCompletion F →ₐ[v.adicCompletion F]
      w.val.adicCompletion M :=
    (Pi.evalAlgHom (v.adicCompletion F)
      (fun w' : v.placesOver M => w'.val.adicCompletion M) w).comp
      (completionTensorProductRightAlgEquiv v).toAlgHom
  have he₀_apply : ∀ a, e₀ a = completionTensorProductRightAlgEquiv v a w :=
    fun a => rfl
  have hbij : Function.Bijective
      (completionTensorProductRightAlgEquiv (K := F) (L := M) v) :=
    (completionTensorProductRightAlgEquiv (K := F) (L := M) v).toEquiv.bijective
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro a b hab
      apply hbij.1
      funext w'
      obtain rfl := huniq w' w
      rw [he₀_apply, he₀_apply] at hab
      exact hab
    · intro y
      obtain ⟨z, hz⟩ := hbij.2 (Function.update 0 w y)
      refine ⟨z, ?_⟩
      rw [he₀_apply, hz, Function.update_self]
  let e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F]
      w.val.adicCompletion M :=
    AlgEquiv.ofBijective e₀ he₀
  have he_apply : ∀ a, e a = completionTensorProductRightAlgEquiv v a w :=
    fun a => rfl
  have he_tmul_one : ∀ x : M, e (x ⊗ₜ[F] 1) =
      algebraMap M (w.val.adicCompletion M) x := by
    intro x
    rw [he_apply]
    exact completionTensorProductRightAlgEquiv_tmul_one v x w
  have hfr : Module.finrank (v.adicCompletion F) (w.val.adicCompletion M) =
      Module.finrank F M :=
    e.toLinearEquiv.finrank_eq.symm.trans
      ((Algebra.TensorProduct.commRight F (v.adicCompletion F)
        M).symm.toLinearEquiv.finrank_eq.trans
        (Module.finrank_baseChange (R := v.adicCompletion F) (S := F) (M' := M)))
  exact ⟨w, e, fun w' => huniq w' w, he_tmul_one, hfr⟩

end IsDedekindDomain.HeightOneSpectrum
