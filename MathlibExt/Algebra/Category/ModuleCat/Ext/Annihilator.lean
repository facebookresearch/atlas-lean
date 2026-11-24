/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Adapted from `TauCeti/Algebra/Category/ModuleCat/Ext/Basic.lean` in
TauCetiProject/TauCeti at commit
62bbc0596dc3539d488232e4e924a338548ea0a9.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Category/ModuleCat/Ext/Basic.lean
The source copyright and Apache 2.0 license notice are retained above.
This port targets Atlas's pinned Mathlib without a TauCeti dependency.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Annihilators of `Ext` groups of modules

For modules `N` and `M` over a commutative ring `R`, the `R`-module `Ext N M n` is killed both by
the annihilator of `N` and by the annihilator of `M`, since multiplication by `r` on `Ext N M n`
is induced by multiplication by `r` on either argument. In particular `Ext N M n` vanishes when
these two annihilators are comaximal, for example `Ext (R ⧸ I) M n = 0` when `I M = M` for a
finite module `M`. A map out of a finite free module with image in `I F`, for an ideal `I` killing
`N`, is a combination of maps with coefficients in `I`, so it induces zero on `Ext N - n`; for
`N` the residue field of a local ring this is the property of minimal free presentations used to
compute depths.

## Main results

* `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_left` and
  `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator_right`: elements of the annihilator
  of either argument act by zero on `Ext N M n`.
* `CategoryTheory.Abelian.Ext.subsingleton_of_annihilator_sup_eq_top`: `Ext N M n` vanishes when
  the annihilators of `N` and `M` are comaximal.
* `CategoryTheory.Abelian.Ext.comp_mk₀_eq_zero_of_range_le_smul_top`: if `I` annihilates `N`, a map
  `K ⟶ F` from a finite free module with image in `I • ⊤` induces zero on `Ext N - n`.
-/

public section

universe v u

open CategoryTheory

namespace CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] {N M : ModuleCat.{v} R}

/-- An element of the annihilator of `N` acts by zero on `Ext N M n`. This restates
`Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` as a statement about the scalar action. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_left {r : R} (hr : r ∈ Module.annihilator R N)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  simpa [Ext.mk₀_smul] using
    congrArg (fun f ↦ f.hom x) (Ext.postcomp_smul_id_eq_zero_of_mem_annihilator (M := M) hr n)

/-- An element of the annihilator of `M` acts by zero on `Ext N M n`. -/
theorem Ext.smul_eq_zero_of_mem_annihilator_right {r : R} (hr : r ∈ Module.annihilator R M)
    {n : ℕ} (x : Ext N M n) : r • x = 0 := by
  have : r • 𝟙 M = 0 := by
    simp [← ModuleCat.lsmul_eq_smul_id, Module.mem_annihilator_iff_lsmul_eq_zero.mp hr]
  simp [Ext.smul_eq_comp_mk₀, this]

/-- `Ext N M n` vanishes when the annihilators of `N` and `M` are comaximal. -/
theorem Ext.subsingleton_of_annihilator_sup_eq_top
    (h : Module.annihilator R N ⊔ Module.annihilator R M = ⊤) (n : ℕ) :
    Subsingleton (Ext N M n) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h ▸ Submodule.mem_top : (1 : R) ∈ _)
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  rw [← one_smul R z, ← hab, add_smul, smul_eq_zero_of_mem_annihilator_left ha,
    smul_eq_zero_of_mem_annihilator_right hb, add_zero]

/-- Let the ideal `I` annihilate `N`, and let `f : K ⟶ F` be a map out of a finite free module
whose image lies in `I • F`. Then `f` induces the zero map `Ext N K n → Ext N F n`. -/
theorem Ext.comp_mk₀_eq_zero_of_range_le_smul_top {K F : ModuleCat.{v} R} [Module.Free R K]
    [Module.Finite R K] {I : Ideal R} (hI : I ≤ Module.annihilator R N) (f : K ⟶ F)
    (hf : LinearMap.range f.hom ≤ I • ⊤) {n : ℕ} (x : Ext N K n) :
    x.comp (Ext.mk₀ f) (add_zero n) = 0 := by
  let b := Module.Free.chooseBasis R K
  -- A rank-one map `k ↦ φ k • y` with `y ∈ I • F` induces zero.
  have key (φ : K →ₗ[R] R) {y : F} (hy : y ∈ I • (⊤ : Submodule R F)) :
      x.comp (Ext.mk₀ (ModuleCat.ofHom (φ.smulRight y))) (add_zero n) = 0 := by
    refine Submodule.smul_induction_on hy (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · have : ModuleCat.ofHom (φ.smulRight (a • y)) = a • ModuleCat.ofHom (φ.smulRight y) := by
        ext k
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_smul, LinearMap.smulRight_apply,
          LinearMap.smul_apply]
        exact smul_comm _ _ _
      rw [this, Ext.mk₀_smul, Ext.comp_smul, smul_eq_zero_of_mem_annihilator_left (hI ha)]
    · have : ModuleCat.ofHom (φ.smulRight (y + z)) =
          ModuleCat.ofHom (φ.smulRight y) + ModuleCat.ofHom (φ.smulRight z) := by
        ext; simp
      rw [this, Ext.mk₀_add, Ext.comp_add, hy, hz, add_zero]
  -- Write `f` as a sum of rank-one maps, using a basis of `K`.
  have hsum : f = ∑ j, ModuleCat.ofHom ((b.coord j).smulRight (f (b j))) := by
    ext1
    refine b.ext fun j ↦ ?_
    simp [Finsupp.single_apply]
  rw [hsum, Ext.mk₀_sum, Ext.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ key _ (hf ⟨b j, rfl⟩)

end CategoryTheory.Abelian
