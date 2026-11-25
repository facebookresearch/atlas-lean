/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.lean`
and
`P2M/Sol/S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.lean`
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

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RepresentationTheory.Coinduced

import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace Rep

open CategoryTheory

universe u v w

/-- A coinduced representation from a finite-index subgroup is finite
dimensional, and its dimension is the index times the dimension of the
original representation: choosing right-coset representatives identifies
the coinduced representation with functions from the coset quotient. -/
public theorem finiteDimensional_coind_and_finrank_coind_eq_index_mul
    {k : Type u} {G : Type v} [Field k] [Group G] (S : Subgroup G)
    [S.FiniteIndex] (N : Rep.{w} k S) [FiniteDimensional k N] :
    FiniteDimensional k (coind S.subtype N) ∧
      Module.finrank k (coind S.subtype N) = S.index * Module.finrank k N := by
  classical
  let Q := Quotient (QuotientGroup.rightRel S)
  haveI : Finite Q :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g =>
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)
  have rep_mul : ∀ (s : S) (g : G), rep ((s : G) * g) = rep g := fun s g => by
    change (Quotient.mk _ ((s : G) * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * g) g
    rw [QuotientGroup.rightRel_apply]
    simp
  have key : ∀ (a : G) (ha : a ∈ S) (v : N), a = 1 → N.ρ ⟨a, ha⟩ v = v := by
    rintro a ha v rfl
    exact congrFun (congrArg DFunLike.coe (map_one N.ρ)) v
  let e : coind S.subtype N ≃ₗ[k] (Q → N) :=
    { toFun := fun f q => (f : G → N) q.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun F => ⟨fun g => N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩
          (F (Quotient.mk _ g)), fun s h => by
        simp only [Subgroup.coe_subtype]
        have hq : (Quotient.mk (QuotientGroup.rightRel S) ((s : G) * h)) =
            Quotient.mk _ h :=
          Quotient.sound (by
            change @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * h) h
            rw [QuotientGroup.rightRel_apply]; simp)
        rw [← Module.End.mul_apply, ← map_mul]
        have hmem : (s : G) * h * (rep ((s : G) * h))⁻¹ ∈ S := rep_spec _
        have hthis : (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, hmem⟩ : S) =
            s * ⟨h * (rep h)⁻¹, rep_spec h⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, rep_mul, mul_assoc]
        rw [show (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, rep_spec _⟩ : S) =
            s * ⟨h * (rep h)⁻¹, rep_spec h⟩ from hthis, hq]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext g
        change N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩
            ((f : G → N) (Quotient.mk (QuotientGroup.rightRel S) g).out) =
          (f : G → N) g
        have hf := f.2 ⟨g * (rep g)⁻¹, rep_spec g⟩ (rep g)
        rw [← hf]
        change (f : G → N) (g * (rep g)⁻¹ * rep g) = (f : G → N) g
        rw [inv_mul_cancel_right]
      right_inv := fun F => by
        funext q
        change N.ρ ⟨q.out * (rep q.out)⁻¹, rep_spec q.out⟩
            (F (Quotient.mk _ q.out)) = F q
        have hout : Quotient.mk (QuotientGroup.rightRel S) q.out = q :=
          Quotient.out_eq q
        rw [hout]
        exact key _ _ _ (by
          change q.out * ((Quotient.mk (QuotientGroup.rightRel S) q.out).out)⁻¹ = 1
          rw [hout, mul_inv_cancel]) }
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Subgroup.index, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]

end Rep
