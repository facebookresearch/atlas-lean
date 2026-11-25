/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.TateOortRankTwo

@[expose] public section

universe u v

open scoped TensorProduct

/-- Exact source statement, with the original universe binders. -/
example {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H] (hrank : Module.finrank R H = 2) :
    ∃ (e : Module.Basis (Fin 2) R H) (a b : R),
      e 0 = 1 ∧ a * b = 2 ∧ Coalgebra.counit (R := R) (e 1) = 0 ∧ e 1 * e 1 = a • e 1 ∧
      Coalgebra.comul (R := R) (e 1) = e 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] e 1 - b • (e 1 ⊗ₜ[R] e 1) ∧
      HopfAlgebra.antipode R (e 1) = e 1 :=
  HopfAlgebra.exists_basis_tateOort_two hrank

/-- A concrete consumer: the rank-two basis has first vector `1`. -/
example {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Free R H] (hrank : Module.finrank R H = 2) :
    ∃ e : Module.Basis (Fin 2) R H, e 0 = 1 :=
  let ⟨e, _a, _b, he0, _⟩ := HopfAlgebra.exists_basis_tateOort_two (R := R) (H := H) hrank
  ⟨e, he0⟩
