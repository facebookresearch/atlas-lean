/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K1.Whitehead
public import MathlibExt.KTheory.Ring.K1.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Whitehead quotient `StableGL / E∞` and comparison with `K₁`

Objectwise layer: the quotient by the stable elementary subgroup and its identification
with `Abelianization (StableGL R)` and hence with `K₁ R`, via
`stableElementarySubgroup_eq_commutator`.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory

/-- Whitehead quotient `StableGL R / E∞(R)` as a quotient group. -/
abbrev WhiteheadQuotient (R : Type u) [Ring R] : Type u :=
  StableGL R ⧸ stableElementarySubgroup R

noncomputable instance instStableElementarySubgroupNormal (R : Type u) [Ring R] :
    (stableElementarySubgroup R).Normal := by
  rw [stableElementarySubgroup_eq_commutator]
  infer_instance

noncomputable instance instWhiteheadQuotientCommGroup (R : Type u) [Ring R] :
    CommGroup (WhiteheadQuotient R) where
  __ := QuotientGroup.Quotient.group _
  mul_comm a b := by
    have hComm : IsMulCommutative (WhiteheadQuotient R) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (commutator_le_stableElementarySubgroup R))
    exact hComm.is_comm.comm a b

/-- Multiplicative identification with the abelianization. -/
noncomputable def WhiteheadQuotient.mulEquivAbelianization (R : Type u) [Ring R] :
    WhiteheadQuotient R ≃* Group.Abelianization (StableGL R) :=
  QuotientGroup.quotientMulEquivOfEq (stableElementarySubgroup_eq_commutator R)

@[simp]
theorem WhiteheadQuotient.mulEquivAbelianization_mk (R : Type u) [Ring R]
    (g : StableGL R) :
    mulEquivAbelianization R (QuotientGroup.mk (s := stableElementarySubgroup R) g) =
      Group.Abelianization.of g :=
  rfl

/-- Additive identification with `K₁ R`. -/
noncomputable def WhiteheadQuotient.addEquivK1 (R : Type u) [Ring R] :
    Additive (WhiteheadQuotient R) ≃+ K1 R :=
  (mulEquivAbelianization (R := R)).toAdditive

@[simp]
theorem WhiteheadQuotient.addEquivK1_of_mk (R : Type u) [Ring R]
    (g : StableGL R) :
    addEquivK1 R (Additive.ofMul (QuotientGroup.mk (s := stableElementarySubgroup R) g)) =
      K1.proj g :=
  rfl

@[simp]
theorem WhiteheadQuotient.addEquivK1_of_mk_finite (R : Type u) [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    addEquivK1 R
        (Additive.ofMul (QuotientGroup.mk (s := stableElementarySubgroup R) (StableGL.of g))) =
      K1.mk g :=
  rfl

end AlgebraicKTheory

end
