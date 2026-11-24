/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder.lean`
and
`P2M/Sol/S_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

@[expose] public section

open AddMonoidAlgebra

namespace ValuationSubring

/-- An algebra map out of a torsion group algebra over a valuation subring
lands in the valuation subring, and hence factors through it.

Each monomial `single g 1` has finite order, so its image is integral over
the valuation subring; a valuation subring of a field is integrally closed,
so the image lies in the subring. The claim for a general element follows
by expanding it in monomials. -/
public theorem addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
    {L : Type*} [Field L] (A : ValuationSubring L)
    {G : Type*} [AddMonoid G] (hG : ∀ g : G, IsOfFinAddOrder g)
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    (∀ x, χ x ∈ A) ∧ ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x := by
  have hsingle : ∀ g : G, χ (single g 1) ∈ A := by
    intro g
    obtain ⟨n, hn, hng⟩ := (hG g).exists_nsmul_eq_zero
    have hpow : χ (single g 1) ^ n = 1 := by
      rw [← map_pow, AddMonoidAlgebra.single_pow, hng, one_pow]
      exact map_one χ
    have hint : IsIntegral A (χ (single g 1)) :=
      IsIntegral.of_pow hn (by rw [hpow]; exact isIntegral_one)
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
    rw [← hy]
    exact y.2
  have hall : ∀ x, χ x ∈ A := by
    intro x
    induction x using AddMonoidAlgebra.induction_on with
    | of g => simpa only [AddMonoidAlgebra.of_apply, toAdd_ofAdd] using hsingle g
    | add f g hf hg => rw [map_add]; exact A.add_mem _ _ hf hg
    | smul r f hf =>
      rw [map_smul, Algebra.smul_def]
      exact A.mul_mem _ _ r.2 hf
  refine ⟨hall, ?_⟩
  refine ⟨{ toFun := fun x => ⟨χ x, hall x⟩, map_one' := ?_, map_mul' := ?_, map_zero' := ?_,
            map_add' := ?_, commutes' := ?_ }, fun x => rfl⟩
  · exact Subtype.ext (map_one χ)
  · intro x y; exact Subtype.ext (map_mul χ x y)
  · exact Subtype.ext (map_zero χ)
  · intro x y; exact Subtype.ext (map_add χ x y)
  · intro a; exact Subtype.ext (χ.commutes a)

end ValuationSubring
