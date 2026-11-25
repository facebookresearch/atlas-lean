/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Ext.Annihilator
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u

variable {R : Type u} [CommRing R]

/-! Elements of `I` act by zero on `Ext (R ⧸ I) M n` and on `Ext N (R ⧸ I) n`. -/

example (I : Ideal R) (M : ModuleCat.{u} R) {r : R} (hr : r ∈ I) {n : ℕ}
    (x : Ext (ModuleCat.of R (R ⧸ I)) M n) : r • x = 0 :=
  Ext.smul_eq_zero_of_mem_annihilator_left (by rwa [Ideal.annihilator_quotient]) x

example (I : Ideal R) (N : ModuleCat.{u} R) {r : R} (hr : r ∈ I) {n : ℕ}
    (x : Ext N (ModuleCat.of R (R ⧸ I)) n) : r • x = 0 :=
  Ext.smul_eq_zero_of_mem_annihilator_right (by rwa [Ideal.annihilator_quotient]) x

/-! Comaximal annihilators: `Ext (R ⧸ I) (R ⧸ J) n` vanishes when `I + J = R`. -/

example (I J : Ideal R) (h : I ⊔ J = ⊤) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ J)) n) :=
  Ext.subsingleton_of_annihilator_sup_eq_top
    (by rwa [Ideal.annihilator_quotient, Ideal.annihilator_quotient]) n

-- A concrete instance: over `ℤ`, every `Ext` group between `ℤ/2` and `ℤ/3` vanishes.
example (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}))
      (ModuleCat.of ℤ (ℤ ⧸ Ideal.span {(3 : ℤ)})) n) := by
  refine Ext.subsingleton_of_annihilator_sup_eq_top ?_ n
  rw [Ideal.annihilator_quotient, Ideal.annihilator_quotient, Ideal.eq_top_iff_one,
    Submodule.mem_sup]
  exact ⟨-2, Ideal.mem_span_singleton.mpr (by norm_num), 3,
    Ideal.mem_span_singleton_self 3, by norm_num⟩

/-! Maps out of a finite free module with image in `I • F` induce zero on `Ext (R ⧸ I) - n`. -/

-- Multiplication by an element of `I` on the free module `R`.
example (I : Ideal R) {r : R} (hr : r ∈ I) {n : ℕ}
    (x : Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) n) :
    x.comp (Ext.mk₀ (r • 𝟙 (ModuleCat.of R R))) (add_zero n) = 0 := by
  refine Ext.comp_mk₀_eq_zero_of_range_le_smul_top
    (by rw [Ideal.annihilator_quotient]) _ ?_ x
  rintro _ ⟨y, rfl⟩
  simpa using Submodule.smul_mem_smul hr (Submodule.mem_top (x := y))

-- The local-ring form used for minimal free presentations: a map from a finite free module
-- whose image lies in `𝔪 • F` induces zero on `Ext k - n`, for `k = R ⧸ 𝔪`.
example [IsLocalRing R] {K F : ModuleCat.{u} R} [Module.Free R K] [Module.Finite R K]
    (f : K ⟶ F) (hf : LinearMap.range f.hom ≤ IsLocalRing.maximalIdeal R • ⊤) {n : ℕ}
    (x : Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) K n) :
    x.comp (Ext.mk₀ f) (add_zero n) = 0 :=
  Ext.comp_mk₀_eq_zero_of_range_le_smul_top (by rw [Ideal.annihilator_quotient]) f hf x
