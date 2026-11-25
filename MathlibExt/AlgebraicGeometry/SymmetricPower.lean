/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_SymmetricPower.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

/-- The `r`-fold fibre product of `C` over `Spec k`, the domain of the
permutation action whose quotient is the `r`-th symmetric power. -/
noncomputable abbrev finFibrePow : Scheme.{u} :=
  widePullback (Spec (CommRingCat.of k)) (fun _ : Fin r => C) (fun _ => c)

namespace finFibrePow

/-- The projection from the fibre power to the `l`-th factor. -/
noncomputable abbrev proj (l : Fin r) : finFibrePow c r ⟶ C :=
  WidePullback.π (fun _ : Fin r => c) l

/-- The structure morphism from the fibre power to `Spec k`. -/
noncomputable abbrev toBase : finFibrePow c r ⟶ Spec (CommRingCat.of k) :=
  WidePullback.base (fun _ : Fin r => c)

@[reassoc]
theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _

/-- The morphism of the fibre power permuting the factors by `σ`. -/
noncomputable def permHom (σ : Equiv.Perm (Fin r)) : finFibrePow c r ⟶ finFibrePow c r :=
  WidePullback.lift (toBase c r) (fun j => proj c r (σ⁻¹ j)) (fun _ => WidePullback.π_arrow _ _)

@[reassoc]
theorem permHom_proj (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    permHom c r σ ≫ proj c r j = proj c r (σ⁻¹ j) :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc]
theorem permHom_toBase (σ : Equiv.Perm (Fin r)) : permHom c r σ ≫ toBase c r = toBase c r :=
  WidePullback.lift_base _ _ _ _

theorem permHom_one : permHom c r 1 = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.id_comp, inv_one, Equiv.Perm.one_apply]
  · rw [permHom_toBase, Category.id_comp]

theorem permHom_mul (σ τ : Equiv.Perm (Fin r)) :
    permHom c r (σ * τ) = permHom c r τ ≫ permHom c r σ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.assoc, permHom_proj, permHom_proj, mul_inv_rev,
      Equiv.Perm.mul_apply]
  · rw [permHom_toBase, Category.assoc, permHom_toBase, permHom_toBase]

/-- The permutation of the factors as an automorphism of the fibre power. -/
noncomputable def permAut (σ : Equiv.Perm (Fin r)) : Aut (finFibrePow c r) :=
  Aut.of ⟨permHom c r σ, permHom c r σ⁻¹,
    by rw [← permHom_mul, inv_mul_cancel, permHom_one],
    by rw [← permHom_mul, mul_inv_cancel, permHom_one]⟩

/-- The action of the permutation group on the fibre power by automorphisms. -/
noncomputable def permAct : Equiv.Perm (Fin r) →* Aut (finFibrePow c r) :=
  MonoidHom.mk' (permAut c r) (fun σ τ => by
    apply Aut.ext
    change (permAut c r (σ * τ)).asIso = (permAut c r τ).asIso.trans (permAut c r σ).asIso
    apply Iso.ext
    exact permHom_mul c r σ τ)

theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).asIso.hom = permHom c r σ := rfl

theorem permAct_inv (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).asIso.inv = permHom c r σ⁻¹ := rfl

@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).asIso.hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).asIso.hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow

theorem le_preimage_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ X) (q : X ⟶ Y) (h : g ≫ q = q)
    (V : Y.Opens) : q ⁻¹ᵁ V ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, h]

end AlgebraicGeometry

namespace AlgebraicCurve

open AlgebraicGeometry

/-- A symmetric power package: a scheme `Csym` equipped with a finite
surjective quotient morphism from the `r`-fold fibre power of `C`, invariant
under permuting the factors, whose sections are exactly the invariant
sections, which is integral, proper over `Spec k`, and smooth of relative
dimension `r` over `Spec k`. -/
structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where

  Csym : Scheme.{u}

  csym : Csym ⟶ Spec (CommRingCat.of k)

  π : finFibrePow c r ⟶ Csym

  π_comp_csym : π ≫ csym = finFibrePow.toBase c r

  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom ≫ π = π

  isFinite_π : IsFinite π

  surjective_π : Surjective π

  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔
      ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom.base x = x'

  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)

  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).asIso.hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}

  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U

  integral : IsIntegral Csym

  proper : IsProper csym

  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve
