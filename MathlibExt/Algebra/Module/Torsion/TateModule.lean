/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import MathlibExt.NumberTheory.Padics.TateModule

/-!
# Torsion levels, the inverse-limit property and functoriality of the Tate module

Adapted from TauCeti/Algebra/Module/Torsion/TateModule.lean,
revision 62bbc0596dc3539d488232e4e924a338548ea0a9, lines 78--309: the torsion-level projections,
the inverse-limit universal property and the maps induced by additive homomorphisms.
Modifications: the source's own carrier (compatible families of torsion points) and its `ℤ_p`
action are replaced by the root carrier `TateModule p A` of
`MathlibExt.NumberTheory.Padics.TateModule` (compatible sequences in `A`) and its `ℤ_p`-module
structure, so the finiteness and freeness results proved there apply directly; namespaces and
imports change accordingly. The original Apache 2.0 copyright and authors above are retained.

References: Silverman, *Arithmetic of Elliptic Curves*, III.7.

## Main definitions

* `MathlibExt.Algebra.Module.Torsion.TateModule.levelProj`: projection to the torsion level
  `A[p^n]`.
* `MathlibExt.Algebra.Module.Torsion.TateModule.liftLevels`: the map determined by compatible
  maps to the torsion levels.
* `MathlibExt.Algebra.Module.Torsion.TateModule.map`,
  `MathlibExt.Algebra.Module.Torsion.TateModule.mapLinearMap`: the additive and `ℤ_p`-linear maps
  induced by an additive homomorphism.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.Algebra.Module.Torsion

variable (p : ℕ) (A : Type*) [AddCommGroup A]

/-- The `n`-th level `A[p^n]` of the `p`-power torsion tower. -/
abbrev TateModuleLevel (n : ℕ) : Type _ :=
  AddSubgroup.torsionBy A ((p ^ n : ℕ) : ℤ)

/-- The transition map `A[p^(n+1)] → A[p^n]`, given by multiplication by `p`. -/
def tateModuleTransition (n : ℕ) :
    TateModuleLevel p A (n + 1) →+ TateModuleLevel p A n where
  toFun x := ⟨p • (x : A), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    rw [← mul_nsmul, ← pow_succ']
    simpa using congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The transition map is multiplication by `p` on the underlying group. -/
@[simp]
theorem tateModuleTransition_apply (n : ℕ) (x : TateModuleLevel p A (n + 1)) :
    (tateModuleTransition p A n x : A) = p • (x : A) :=
  (rfl)

namespace TateModule

variable {p A}

/-- Projection of a Tate-module point to its `p^n`-torsion level. -/
def levelProj (n : ℕ) : _root_.TateModule p A →+ TateModuleLevel p A n where
  toFun x := ⟨(x : ℕ → A) n, _root_.TateModule.torsion x n⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The torsion-level projection is the `n`-th component. -/
@[simp]
theorem coe_levelProj (n : ℕ) (x : _root_.TateModule p A) :
    (levelProj n x : A) = (x : ℕ → A) n :=
  rfl

/-- Consecutive torsion-level components are compatible under multiplication by `p`. -/
@[simp]
theorem levelProj_succ (x : _root_.TateModule p A) (n : ℕ) :
    tateModuleTransition p A n (levelProj (n + 1) x) = levelProj n x :=
  Subtype.ext <| by
    rw [tateModuleTransition_apply, coe_levelProj, coe_levelProj, ← natCast_zsmul]
    exact _root_.TateModule.compat x n

/-- A Tate-module point is determined by its torsion-level components. -/
theorem ext_levelProj {x y : _root_.TateModule p A} (h : ∀ n, levelProj n x = levelProj n y) :
    x = y :=
  Subtype.ext (funext fun n ↦ congrArg Subtype.val (h n))

/-- The Tate-module point with prescribed compatible torsion-level components. -/
def ofLevels (x : ∀ n, TateModuleLevel p A n)
    (hx : ∀ n, tateModuleTransition p A n (x (n + 1)) = x n) : _root_.TateModule p A :=
  ⟨fun n ↦ (x n : A), fun n ↦ ⟨(x n).property, by
    rw [natCast_zsmul]
    exact (tateModuleTransition_apply p A n (x (n + 1))).symm.trans
      (congrArg Subtype.val (hx n))⟩⟩

/-- The torsion-level projection of `ofLevels` is the prescribed component. -/
@[simp]
theorem levelProj_ofLevels (x : ∀ n, TateModuleLevel p A n)
    (hx : ∀ n, tateModuleTransition p A n (x (n + 1)) = x n) (n : ℕ) :
    levelProj n (ofLevels x hx) = x n :=
  rfl

section Lift

variable {B : Type*} [AddZeroClass B]
  (f : ∀ n, B →+ TateModuleLevel p A n)
  (hf : ∀ n, (tateModuleTransition p A n).comp (f (n + 1)) = f n)

/-- The additive homomorphism into the Tate module determined by compatible maps to its torsion
levels: the inverse-limit universal property. -/
def liftLevels : B →+ _root_.TateModule p A where
  toFun b := ofLevels (fun n ↦ f n b) fun n ↦ DFunLike.congr_fun (hf n) b
  map_zero' := ext_levelProj fun n ↦ by simp
  map_add' a b := ext_levelProj fun n ↦ by simp

/-- Projection after `liftLevels` recovers the corresponding torsion-level map. -/
@[simp]
theorem levelProj_comp_liftLevels (n : ℕ) : (levelProj n).comp (liftLevels f hf) = f n :=
  (rfl)

/-- The lift of a compatible family of torsion-level maps is unique. -/
theorem liftLevels_unique (g : B →+ _root_.TateModule p A)
    (hg : ∀ n, (levelProj n).comp g = f n) : g = liftLevels f hf :=
  AddMonoidHom.ext fun b ↦ ext_levelProj fun n ↦
    (DFunLike.congr_fun (hg n) b).trans
      (DFunLike.congr_fun (levelProj_comp_liftLevels f hf n) b).symm

end Lift

section Map

variable {B : Type*} [AddCommGroup B]

/-- An additive homomorphism induces an additive homomorphism of Tate modules, componentwise. -/
def map (f : A →+ B) : _root_.TateModule p A →+ _root_.TateModule p B where
  toFun x := ⟨fun n ↦ f ((x : ℕ → A) n), fun n ↦
    ⟨by rw [← map_zsmul, _root_.TateModule.torsion, map_zero],
      by rw [← map_zsmul, _root_.TateModule.compat]⟩⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero f)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add f _ _)

/-- The induced map is computed componentwise. -/
@[simp]
theorem map_apply_coe (f : A →+ B) (x : _root_.TateModule p A) (n : ℕ) :
    ((map f x : _root_.TateModule p B) : ℕ → B) n = f ((x : ℕ → A) n) :=
  rfl

/-- On torsion levels, the induced map is the original homomorphism. -/
@[simp]
theorem coe_levelProj_map (f : A →+ B) (x : _root_.TateModule p A) (n : ℕ) :
    (levelProj n (map f x) : B) = f (levelProj n x) :=
  rfl

/-- Tate modules send identity homomorphisms to identity homomorphisms. -/
@[simp]
theorem map_id : map (p := p) (AddMonoidHom.id A) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ rfl

/-- Tate modules send compositions to compositions. -/
@[simp]
theorem map_comp {C : Type*} [AddCommGroup C] (g : B →+ C) (f : A →+ B) :
    map (p := p) (g.comp f) = (map (p := p) g).comp (map (p := p) f) :=
  AddMonoidHom.ext fun _ ↦ rfl

variable [Fact p.Prime]

/-- An additive homomorphism induces a `ℤ_p`-linear map on Tate modules. -/
def mapLinearMap (f : A →+ B) : _root_.TateModule p A →ₗ[ℤ_[p]] _root_.TateModule p B where
  toFun := map f
  map_add' := map_add (map f)
  map_smul' a x := Subtype.ext <| funext fun n ↦ by
    change f (((a.appr n : ℕ) : ℤ) • (x : ℕ → A) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → A) n)
    exact map_zsmul f _ _

/-- The linear map induced on Tate modules has the same underlying additive map as `map`. -/
@[simp]
theorem mapLinearMap_apply (f : A →+ B) (x : _root_.TateModule p A) :
    mapLinearMap f x = map f x :=
  rfl

end Map

end TateModule

end MathlibExt.Algebra.Module.Torsion
