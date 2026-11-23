/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Module.Torsion.TateModule
public import MathlibExt.NumberTheory.Padics.TateModule

/-!
# Comparison of the two Tate-module carriers

`MathlibExt.Algebra.Module.Torsion.TateModule p A`, ported from Tau Ceti, stores compatible
families of points of the torsion subgroups `A[p^n]`. The root `TateModule p A` stores compatible
sequences in `A` together with their torsion conditions. Both are the inverse limit of the
`A[p^n]` under multiplication by `p`, with the `ℤ_p`-action reducing a scalar modulo `p^n` on the
`n`-th component.

This file identifies the two carriers by a `ℤ_p`-linear equivalence that is the identity on every
finite component and is natural in `A`, so results proved for either carrier apply to the other.

## Main definitions

* `MathlibExt.Algebra.Module.Torsion.TateModule.equivRoot`: the additive equivalence with the root
  carrier.
* `MathlibExt.Algebra.Module.Torsion.TateModule.linearEquivRoot`: the same map as a `ℤ_p`-linear
  equivalence.

## Main results

* `MathlibExt.Algebra.Module.Torsion.TateModule.equivRoot_apply_coe`: the equivalence is the
  identity on finite components.
* `MathlibExt.Algebra.Module.Torsion.TateModule.equivRoot_map`: naturality for the maps induced by
  additive homomorphisms.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.Algebra.Module.Torsion.TateModule

variable {p : ℕ} {A : Type*} [AddCommGroup A]

/-- The underlying compatible sequence of a point, as a point of the root carrier. -/
def toRoot (x : TateModule p A) : _root_.TateModule p A :=
  ⟨fun n ↦ (proj n x : A), fun n ↦ ⟨(proj n x).property, by
    rw [natCast_zsmul]
    exact (tateModuleTransition_apply p A n (proj (n + 1) x)).symm.trans
      (congrArg Subtype.val (proj_succ x n))⟩⟩

/-- The point with the components of a compatible sequence of the root carrier. -/
def ofRoot (y : _root_.TateModule p A) : TateModule p A :=
  mk (fun n ↦ ⟨(y : ℕ → A) n, _root_.TateModule.torsion y n⟩) fun n ↦ Subtype.ext <| by
    rw [tateModuleTransition_apply, ← natCast_zsmul]
    exact _root_.TateModule.compat y n

/-- The two carriers of the Tate module are additively equivalent, componentwise. -/
def equivRoot : TateModule p A ≃+ _root_.TateModule p A where
  toFun := toRoot
  invFun := ofRoot
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The comparison is the identity on every finite component. -/
@[simp]
theorem equivRoot_apply_coe (x : TateModule p A) (n : ℕ) :
    ((equivRoot x : _root_.TateModule p A) : ℕ → A) n = (proj n x : A) :=
  rfl

/-- The inverse comparison is the identity on every finite component. -/
@[simp]
theorem proj_equivRoot_symm_apply (y : _root_.TateModule p A) (n : ℕ) :
    (proj n (equivRoot.symm y) : A) = (y : ℕ → A) n :=
  rfl

/-- The comparison intertwines the finite projections of the two carriers. -/
theorem root_proj_equivRoot (x : TateModule p A) (n : ℕ) :
    _root_.TateModule.proj p A n (equivRoot x) = (proj n x : A) :=
  rfl

/-- The comparison is natural for the maps induced by additive homomorphisms. -/
theorem equivRoot_map {B : Type*} [AddCommGroup B] (f : A →+ B) (x : TateModule p A) (n : ℕ) :
    ((equivRoot (map (p := p) f x) : _root_.TateModule p B) : ℕ → B) n =
      f (((equivRoot x : _root_.TateModule p A) : ℕ → A) n) :=
  rfl

variable [Fact p.Prime]

/-- Reduction modulo `p^n` acts on the `n`-th torsion level through the approximation of the
scalar by a natural number. -/
theorem coe_toZModPow_smul (n : ℕ) (a : ℤ_[p]) (y : TateModuleLevel p A n) :
    ((PadicInt.toZModPow n a • y : TateModuleLevel p A n) : A) =
      ((a.appr n : ℕ) : ℤ) • (y : A) := by
  rw [_root_.TateModule.toZModPow_eq_appr, Nat.cast_smul_eq_nsmul, AddSubgroup.coe_nsmul,
    natCast_zsmul]

/-- The two carriers of the Tate module are `ℤ_p`-linearly equivalent, componentwise. -/
def linearEquivRoot : TateModule p A ≃ₗ[ℤ_[p]] _root_.TateModule p A where
  __ := equivRoot
  map_smul' a x := Subtype.ext <| funext fun n ↦ by
    change ((proj n (a • x) : TateModuleLevel p A n) : A) =
      ((a.appr n : ℕ) : ℤ) • (proj n x : A)
    rw [proj_smul, coe_toZModPow_smul]

@[simp]
theorem linearEquivRoot_apply (x : TateModule p A) :
    linearEquivRoot x = equivRoot x :=
  rfl

@[simp]
theorem linearEquivRoot_symm_apply (y : _root_.TateModule p A) :
    linearEquivRoot.symm y = equivRoot.symm y :=
  rfl

/-- The `ℤ_p`-linear maps induced by additive homomorphisms correspond under the comparison. -/
theorem linearEquivRoot_mapLinearMap {B : Type*} [AddCommGroup B] (f : A →+ B)
    (x : TateModule p A) (n : ℕ) :
    ((linearEquivRoot (mapLinearMap (p := p) f x) : _root_.TateModule p B) : ℕ → B) n =
      f (((linearEquivRoot x : _root_.TateModule p A) : ℕ → A) n) :=
  rfl

end MathlibExt.Algebra.Module.Torsion.TateModule
