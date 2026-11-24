/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_card_algHom_le_finrank_residueField_tensorProduct.lean`
and
`P2M/Sol/S_Algebra_card_algHom_le_finrank_residueField_tensorProduct.lean`
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

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open TensorProduct

namespace Algebra

/-- The number of algebra maps from a finite algebra over a local ring to
an arbitrary target field is bounded by the dimension of the special fibre.

No flatness hypothesis on the algebra and no algebraic closedness
hypothesis on the target field are assumed: maps to the target are
identified with maps out of the base change to the target, where they are
linearly independent as linear maps, and the base change to the target is
spanned by the images of a basis of the special fibre. -/
public theorem card_algHom_le_finrank_residueField_tensorProduct
    (R : Type*) [CommRing R] [IsLocalRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Ω : Type*) [Field Ω] [Algebra R Ω] :
    Finite (B →ₐ[R] Ω) ∧
      Nat.card (B →ₐ[R] Ω) ≤
        Module.finrank (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) B) := by
  classical
  set κ := IsLocalRing.ResidueField R with hκ
  set d := Module.finrank κ (TensorProduct R κ B) with hd
  let bκ : Module.Basis (Fin d) κ (TensorProduct R κ B) :=
    Module.finBasis κ (TensorProduct R κ B)
  have hsurj : Function.Surjective (TensorProduct.mk R κ B 1) :=
    TensorProduct.mk_surjective R B κ Ideal.Quotient.mk_surjective
  choose f hf using fun i : Fin d => hsurj (bκ i)
  have hspanR : Submodule.span R (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f bκ (fun i => hf i)
  have hspanΩ : Submodule.span Ω (Set.range fun i : Fin d => (1 : Ω) ⊗ₜ[R] f i) = ⊤ := by
    have h := Submodule.baseChange_span (R := R) (M := B) Ω (Set.range f)
    rw [hspanR, Submodule.baseChange_top] at h
    rw [← Set.range_comp] at h
    exact h.symm
  have hfinΩ : Module.finrank Ω (TensorProduct R Ω B) ≤ d := by
    have h1 := finrank_range_le_card (R := Ω) (M := TensorProduct R Ω B)
      (fun i : Fin d => (1 : Ω) ⊗ₜ[R] f i)
    rw [Set.finrank, hspanΩ, finrank_top, Fintype.card_fin] at h1
    exact h1
  let e : (B →ₐ[R] Ω) ≃ (TensorProduct R Ω B →ₐ[Ω] Ω) := AlgHom.liftEquiv R Ω B Ω
  have hli : LinearIndependent Ω
      (AlgHom.toLinearMap : (TensorProduct R Ω B →ₐ[Ω] Ω) → TensorProduct R Ω B →ₗ[Ω] Ω) :=
    linearIndependent_algHom_toLinearMap Ω (TensorProduct R Ω B) Ω
  haveI hfin : Finite (TensorProduct R Ω B →ₐ[Ω] Ω) := hli.finite_of_isNoetherian
  haveI : Finite (B →ₐ[R] Ω) := Finite.of_equiv _ e.symm
  refine ⟨inferInstance, ?_⟩
  haveI : Fintype (TensorProduct R Ω B →ₐ[Ω] Ω) := Fintype.ofFinite _
  have hcard : Fintype.card (TensorProduct R Ω B →ₐ[Ω] Ω) ≤
      Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) := hli.fintype_card_le_finrank
  have hdual : Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) =
      Module.finrank Ω (TensorProduct R Ω B) :=
    Subspace.dual_finrank_eq
  calc Nat.card (B →ₐ[R] Ω) = Nat.card (TensorProduct R Ω B →ₐ[Ω] Ω) := Nat.card_congr e
    _ = Fintype.card (TensorProduct R Ω B →ₐ[Ω] Ω) := Nat.card_eq_fintype_card
    _ ≤ Module.finrank Ω (TensorProduct R Ω B →ₗ[Ω] Ω) := hcard
    _ = Module.finrank Ω (TensorProduct R Ω B) := hdual
    _ ≤ d := hfinΩ

end Algebra
