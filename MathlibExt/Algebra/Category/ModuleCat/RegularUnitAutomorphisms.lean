/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Regular-module automorphisms over rings with trivial units

A regular-module automorphism is multiplication by a coefficient unit. A
trivial unit group therefore makes every such automorphism the identity and
every pair of regular-module isomorphism generators equal.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u

namespace ModuleCat

private theorem regularHom_apply {R : Type u} [Ring R]
    (f : ModuleCat.of R R ⟶ ModuleCat.of R R) (r : R) :
    f.hom r = r * f.hom 1 := by
  simpa only [smul_eq_mul, mul_one] using f.hom.map_smul r (1 : R)

/-- A trivial coefficient unit group makes every regular-module automorphism the identity. -/
theorem regularIso_hom_eq_id {R : Type u} [Ring R] [Subsingleton Rˣ]
    (e : ModuleCat.of R R ≅ ModuleCat.of R R) : e.hom = 𝟙 _ := by
  let a : R := e.hom.hom 1
  let b : R := e.inv.hom 1
  have hab : a * b = 1 := by
    have h := ConcreteCategory.congr_hom e.hom_inv_id (1 : R)
    change e.inv.hom (e.hom.hom 1) = 1 at h
    exact (regularHom_apply e.inv a).symm.trans h
  have hba : b * a = 1 := by
    have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : R)
    change e.hom.hom (e.inv.hom 1) = 1 at h
    exact (regularHom_apply e.hom b).symm.trans h
  let scalar : Rˣ := ⟨a, b, hab, hba⟩
  have ha : a = 1 := congrArg (fun z : Rˣ => z.val) (Subsingleton.elim scalar 1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change e.hom.hom r = r
  rw [regularHom_apply]
  change r * a = r
  rw [ha, mul_one]

/-- Actual isomorphism generators of any module agree when the coefficient unit group is trivial. -/
theorem isIso_regular_hom_unique {R : Type u} [Ring R] [Subsingleton Rˣ]
    {M : ModuleCat.{u} R} (f g : ModuleCat.of R R ⟶ M) [IsIso f] [IsIso g] : f = g := by
  have hfg : f ≫ inv g = 𝟙 _ := regularIso_hom_eq_id (asIso f ≪≫ (asIso g).symm)
  apply (cancel_mono (inv g)).mp
  exact hfg.trans (IsIso.hom_inv_id g).symm

end ModuleCat
