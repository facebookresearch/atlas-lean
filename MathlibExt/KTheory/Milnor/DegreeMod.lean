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

public import MathlibExt.KTheory.Milnor.Grading
public import Mathlib.Algebra.Module.ZMod

/-!
# Mod-ℓ quotient of degree pieces

The quotient `DegreeMod F n ℓ := (degree F n) / ℓ·(degree F n)` with its
projection, `ℓ`-torsion property, `ZMod ℓ`-module structure, and transport
along degree equalities.

`DegreeMod` is a transparent additive quotient
`↥(degree F n) ⧸ ellMultiples F n ℓ` so that the standard quotient additive
group and `ZMod` module APIs remain available without a duplicate wrapper
layer. The submodule view `ellMultiplesSubmodule` is the `ℤ`-submodule
presentation of `ellMultiples`, `DegreeMod.mkLinear` is the linear projection
underlying `DegreeMod.mk`, and `DegreeMod.submoduleQuotientEquiv` is the
`ℤ`-linear equivalence to the submodule quotient needed for
`LinearMap.liftQ₂`.

## Main definitions
* `ellMultiples`
* `ellMultiplesSubmodule`
* `DegreeMod`
* `DegreeMod.mk`
* `DegreeMod.mkLinear`
* `DegreeMod.submoduleQuotientEquiv`
* `DegreeMod.castEquiv`
* `DegreeMod.castEq`

## Main results
* `DegreeMod.mk_surjective`
* `DegreeMod.mkLinear_apply`
* `DegreeMod.submoduleQuotientEquiv_apply_mk`
* `DegreeMod.nsmul_eq_zero`
* `DegreeMod.instModuleZMod`
* `DegreeMod.castEquiv_rfl`
* `DegreeMod.castEquiv_symm`
* `DegreeMod.castEquiv_trans`
* `DegreeMod.castEquiv_apply_mk`
* `DegreeMod.castEq_rfl`
* `DegreeMod.castEq_mk`
* `DegreeMod.castEq_mk_struct`
* `DegreeMod.castEq_trans`
* `DegreeMod.castEq_trans_symm`
* `DegreeMod.castEq_symm_trans`
* `DegreeMod.castEq_add`
* `DegreeMod.castEq_neg`
* `DegreeMod.castEq_sub`
* `DegreeMod.castEq_nsmul`
* `DegreeMod.castEq_zsmul`
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable (F : Type*) [Field F]

/-- Subgroup of `ℓ`-multiples in `degree F n`. -/
def ellMultiples (n ℓ : ℕ) : AddSubgroup ↥(degree F n) :=
  (zsmulAddGroupHom (α := ↥(degree F n)) (ℓ : ℤ)).range

/-- Submodule of `ℓ`-multiples in `degree F n`, as the `ℤ`-submodule view of
`ellMultiples F n ℓ` via `AddSubgroup.toIntSubmodule`. -/
def ellMultiplesSubmodule (n ℓ : ℕ) : Submodule ℤ (degree F n) :=
  (ellMultiples F n ℓ).toIntSubmodule

/-- Mod-`ℓ` quotient `degree F n / ℓ·(degree F n)` as the additive
quotient `↥(degree F n) ⧸ ellMultiples F n ℓ`. -/
abbrev DegreeMod (n ℓ : ℕ) : Type _ :=
  ↥(degree F n) ⧸ ellMultiples F n ℓ

/-- Projection `degree F n → DegreeMod F n ℓ`. -/
def DegreeMod.mk (n ℓ : ℕ) : ↥(degree F n) →+ DegreeMod F n ℓ :=
  QuotientAddGroup.mk' (ellMultiples F n ℓ)

/-- Linear quotient projection `degree F n →ₗ[ℤ] DegreeMod F n ℓ`,
the `ℤ`-linear map underlying `DegreeMod.mk`. -/
def DegreeMod.mkLinear (n ℓ : ℕ) : (degree F n) →ₗ[ℤ] DegreeMod F n ℓ :=
  (DegreeMod.mk F n ℓ).toIntLinearMap

/-- `mkLinear` agrees with `mk` as a function. -/
@[simp]
theorem DegreeMod.mkLinear_apply (n ℓ : ℕ) (x : degree F n) :
    DegreeMod.mkLinear F n ℓ x = DegreeMod.mk F n ℓ x :=
  rfl

/-- Linear equivalence between the preserved additive quotient
`DegreeMod F n ℓ` and the submodule quotient
`(degree F n) ⧸ ellMultiplesSubmodule F n ℓ`. It is obtained from the
identity additive equivalence via `QuotientAddGroup.congr` and
`AddEquiv.toIntLinearEquiv`; the subgroup equality uses
`AddSubgroup.toIntSubmodule_toAddSubgroup`. -/
def DegreeMod.submoduleQuotientEquiv (n ℓ : ℕ) :
    DegreeMod F n ℓ ≃ₗ[ℤ] ((degree F n) ⧸ ellMultiplesSubmodule F n ℓ) :=
  (QuotientAddGroup.congr (ellMultiples F (n := n) ℓ)
      (ellMultiplesSubmodule F (n := n) ℓ).toAddSubgroup
      (AddEquiv.refl (degree F n))
      (by
        have h_toAdd : (ellMultiplesSubmodule F (n := n) ℓ).toAddSubgroup =
            ellMultiples F (n := n) ℓ := by
          rw [ellMultiplesSubmodule, AddSubgroup.toIntSubmodule_toAddSubgroup]
        have h_map : (ellMultiples F (n := n) ℓ).map
            (AddEquiv.refl (degree F n)).toAddMonoidHom =
            ellMultiples F (n := n) ℓ := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact hy
          · intro hx
            exact ⟨x, hx, rfl⟩
        exact h_map.trans h_toAdd.symm)).toIntLinearEquiv

/-- Computation of `submoduleQuotientEquiv` on representatives: it sends
`DegreeMod.mk x` to the submodule quotient projection `mkQ x`, suitable for
precomposition with `LinearMap.liftQ₂`. -/
@[simp]
theorem DegreeMod.submoduleQuotientEquiv_apply_mk (n ℓ : ℕ)
    (x : degree F n) :
    DegreeMod.submoduleQuotientEquiv F n ℓ (DegreeMod.mk F n ℓ x) =
      (ellMultiplesSubmodule F n ℓ).mkQ x :=
  rfl

/-- `DegreeMod.mk` is surjective. -/
theorem DegreeMod.mk_surjective (n ℓ : ℕ) :
    Function.Surjective (DegreeMod.mk F n ℓ) :=
  QuotientAddGroup.mk'_surjective _

/-- Every class in `DegreeMod` is `ℓ`-torsion. -/
theorem DegreeMod.nsmul_eq_zero (n ℓ : ℕ) (q : DegreeMod F n ℓ) :
    ℓ • q = 0 := by
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have hx : (ℓ • x) ∈ ellMultiples F n ℓ := by
      rw [ellMultiples]
      exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
    calc
      ℓ • (DegreeMod.mk F n ℓ x) = DegreeMod.mk F n ℓ (ℓ • x) :=
        (map_nsmul (DegreeMod.mk F n ℓ) ℓ x).symm
      _ = 0 :=
        (QuotientAddGroup.eq_zero_iff (x := ℓ • x)).mpr hx

/-- `DegreeMod` as a `ZMod ℓ`-module. -/
instance DegreeMod.instModuleZMod (n ℓ : ℕ) :
    Module (ZMod ℓ) (DegreeMod F n ℓ) :=
  QuotientAddGroup.zmodModule (H := ellMultiples F n ℓ) (by
    intro x
    rw [ellMultiples]
    exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)

/-- Transport equivalence for `DegreeMod` along `m = n`. -/
def DegreeMod.castEquiv {m n ℓ : ℕ} (h : m = n) :
    DegreeMod F m ℓ ≃ₗ[ZMod ℓ] DegreeMod F n ℓ :=
  LinearEquiv.cast (R := ZMod ℓ) (M := fun k => DegreeMod F k ℓ) h

/-- `castEquiv rfl` equals `refl`. -/
@[simp] theorem DegreeMod.castEquiv_rfl {m ℓ : ℕ} :
    DegreeMod.castEquiv (F := F) (m := m) (n := m) (ℓ := ℓ) rfl =
      LinearEquiv.refl (ZMod ℓ) _ := by
  ext x; cases rfl; rfl

/-- Symmetry for `castEquiv`. -/
@[simp] theorem DegreeMod.castEquiv_symm {m n ℓ : ℕ} (h : m = n) :
    (DegreeMod.castEquiv (F := F) (m := m) (n := n) (ℓ := ℓ) h).symm =
      DegreeMod.castEquiv (F := F) h.symm := by
  cases h; ext x; rfl

/-- Transitivity for `castEquiv`. -/
@[simp] theorem DegreeMod.castEquiv_trans {l m n ℓ : ℕ} (h₁ : l = m) (h₂ : m = n) :
    (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₁).trans
        (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₂) =
      DegreeMod.castEquiv (F := F) (ℓ := ℓ) (h₁.trans h₂) := by
  cases h₁; cases h₂; ext x; rfl

/-- `castEquiv` applied to `mk`. -/
@[simp] theorem DegreeMod.castEquiv_apply_mk {m n ℓ : ℕ} (h : m = n)
    (x : ↥(degree F m)) :
    DegreeMod.castEquiv (F := F) (ℓ := ℓ) h (DegreeMod.mk F m ℓ x) =
      DegreeMod.mk F n ℓ (degreeCastEquiv F h x) := by
  cases h; simp [DegreeMod.castEquiv, degreeCastEquiv]

/-- Transport for `DegreeMod` classes along `m = n`. -/
def DegreeMod.castEq {m n ℓ : ℕ} (h : m = n) (q : DegreeMod F m ℓ) :
    DegreeMod F n ℓ :=
  DegreeMod.castEquiv (F := F) h q

/-- `castEq rfl` is identity. -/
theorem DegreeMod.castEq_rfl {m ℓ : ℕ} (q : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) (m := m) (n := m) (ℓ := ℓ) rfl q = q := by
  simp [DegreeMod.castEq]

/-- Low-level raw-`cast` computation of `castEq` on `mk`: expressed via Lean's
dependent `cast`. Use `castEq_mk_struct` for the preferred structural version
through `degreeCastEquiv`. -/
@[simp] theorem DegreeMod.castEq_mk {m n ℓ : ℕ} (h : m = n) (x : degree F m) :
    DegreeMod.castEq (F := F) h (DegreeMod.mk F m ℓ x) =
      DegreeMod.mk F n ℓ (cast (congrArg (fun k => ↥(degree F k)) h) x) := by
  cases h; rfl

/-- Preferred structural rewrite of `castEq` on `mk` via `degreeCastEquiv`.
This is the structural form; `castEq_mk` is the low-level raw-`cast` computation. -/
theorem DegreeMod.castEq_mk_struct {m n ℓ : ℕ} (h : m = n) (x : degree F m) :
    DegreeMod.castEq (F := F) h (DegreeMod.mk F m ℓ x) =
      DegreeMod.mk F n ℓ (degreeCastEquiv F h x) := by
  rw [DegreeMod.castEq_mk, degreeCastEquiv_apply]

/-- Composition of two successive `castEq` transports. -/
@[simp] theorem DegreeMod.castEq_trans {l m n ℓ : ℕ} (h₁ : l = m) (h₂ : m = n)
    (q : DegreeMod F l ℓ) :
    DegreeMod.castEq (F := F) h₂ (DegreeMod.castEq (F := F) h₁ q) =
      DegreeMod.castEq (F := F) (h₁.trans h₂) q := by
  change (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₂)
      ((DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₁) q) =
    (DegreeMod.castEquiv (F := F) (ℓ := ℓ) (h₁.trans h₂)) q
  have htrans := DegreeMod.castEquiv_trans (F := F) (ℓ := ℓ) h₁ h₂
  calc
    (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₂)
        ((DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₁) q) =
      ((DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₁).trans
          (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h₂)) q := rfl
    _ = (DegreeMod.castEquiv (F := F) (ℓ := ℓ) (h₁.trans h₂)) q := by
        rw [htrans]

/-- Cancellation: `castEq h` then `castEq h.symm` is identity. -/
@[simp] theorem DegreeMod.castEq_trans_symm {m n ℓ : ℕ} (h : m = n)
    (q : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h.symm (DegreeMod.castEq (F := F) h q) = q := by
  cases h; rfl

/-- Cancellation: `castEq h.symm` then `castEq h` is identity. -/
@[simp] theorem DegreeMod.castEq_symm_trans {m n ℓ : ℕ} (h : m = n)
    (q : DegreeMod F n ℓ) :
    DegreeMod.castEq (F := F) h (DegreeMod.castEq (F := F) h.symm q) = q := by
  cases h; rfl

/-- `castEq` preserves addition. -/
theorem DegreeMod.castEq_add {m n ℓ : ℕ} (h : m = n) (a b : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h (a + b) =
      DegreeMod.castEq (F := F) h a + DegreeMod.castEq (F := F) h b :=
  map_add _ _ _

/-- `castEq` preserves negation. -/
@[simp] theorem DegreeMod.castEq_neg {m n ℓ : ℕ} (h : m = n)
    (a : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h (-a) = -DegreeMod.castEq (F := F) h a := by
  change (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) (-a) =
    -(DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) a
  rw [map_neg]

/-- `castEq` preserves subtraction. -/
@[simp] theorem DegreeMod.castEq_sub {m n ℓ : ℕ} (h : m = n)
    (a b : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h (a - b) =
      DegreeMod.castEq (F := F) h a - DegreeMod.castEq (F := F) h b := by
  change (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) (a - b) =
    (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) a -
      (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) b
  rw [map_sub]

/-- `castEq` preserves natural number scalar multiplication. -/
@[simp] theorem DegreeMod.castEq_nsmul {m n ℓ : ℕ} (h : m = n) (k : ℕ)
    (a : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h (k • a) = k • DegreeMod.castEq (F := F) h a := by
  change (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) (k • a) =
    k • (DegreeMod.castEquiv (F := F) (ℓ := ℓ) h) a
  rw [map_nsmul]

/-- `castEq` preserves `ℤ` scalar multiplication. -/
theorem DegreeMod.castEq_zsmul {m n ℓ : ℕ} (h : m = n) (c : ℤ)
    (a : DegreeMod F m ℓ) :
    DegreeMod.castEq (F := F) h (c • a) = c • DegreeMod.castEq (F := F) h a :=
  map_zsmul _ _ _

end MilnorKRing
end MilnorK
