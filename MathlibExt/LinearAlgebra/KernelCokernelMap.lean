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

public import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.Abel

/-!
# Maps on kernels and cokernels of linear endomorphisms

A commuting square of linear endomorphisms induces maps on their kernels and
cokernels.  For a short exact sequence carrying compatible endomorphisms, the
induced kernel pair is exact at the middle kernel and the induced cokernel
pair is exact at the middle cokernel.

These are the elementary linear-map boundaries used with the module snake
lemma and finite-length Euler characteristics.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- A commuting square of endomorphisms induces a map on kernels. -/
def mapKer (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) :
    dM.ker →ₗ[R] dN.ker :=
  (f.comp dM.ker.subtype).codRestrict dN.ker fun x => by
    rw [mem_ker]
    have hx : dN (f x) = f (dM x) := by
      simpa only [comp_apply] using
        congrArg (fun k : M →ₗ[R] N => k x) h
    exact hx.trans <| (congrArg f (mem_ker.mp x.property)).trans f.map_zero

@[simp]
theorem mapKer_apply_coe
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (x : dM.ker) :
    (mapKer dM dN f h x : N) = f x :=
  rfl

/-- A commuting square of endomorphisms induces a map on cokernels, modeled
as quotients by their ranges. -/
def mapCoker (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) :
    (M ⧸ dM.range) →ₗ[R] (N ⧸ dN.range) :=
  dM.range.mapQ dN.range f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, congrArg (fun k : M →ₗ[R] N => k x) h⟩)

@[simp]
theorem mapCoker_mk
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) (x : M) :
    mapCoker dM dN f h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  rfl

/-- An injective middle map induces an injective map on kernels. -/
theorem mapKer_injective
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (hf : Function.Injective f) :
    Function.Injective (mapKer dM dN f h) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  simpa only [mapKer_apply_coe] using congrArg Subtype.val hxy

/-- A surjective middle map induces a surjective map on cokernels. -/
theorem mapCoker_surjective
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (hf : Function.Surjective f) :
    Function.Surjective (mapCoker dM dN f h) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective dN.range y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, mapCoker_mk dM dN f h x⟩

theorem equiv_symm_comm
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (e : M ≃ₗ[R] N) (h : dN.comp e.toLinearMap = e.toLinearMap.comp dM) :
    dM.comp e.symm.toLinearMap = e.symm.toLinearMap.comp dN := by
  apply LinearMap.ext
  intro y
  apply e.injective
  have hy := congrArg (fun k : M →ₗ[R] N => k (e.symm y)) h
  change dN (e (e.symm y)) = e (dM (e.symm y)) at hy
  calc
    e (dM (e.symm y)) = dN (e (e.symm y)) := hy.symm
    _ = dN y := congrArg dN (e.apply_symm_apply y)
    _ = e (e.symm (dN y)) := (e.apply_symm_apply (dN y)).symm

/-- A commuting linear equivalence induces an equivalence of kernels. -/
noncomputable def kerEquiv
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (e : M ≃ₗ[R] N) (h : dN.comp e.toLinearMap = e.toLinearMap.comp dM) :
    dM.ker ≃ₗ[R] dN.ker :=
  LinearEquiv.ofLinearMap
    (mapKer dM dN e.toLinearMap h)
    (mapKer dN dM e.symm.toLinearMap (equiv_symm_comm dM dN e h))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact e.apply_symm_apply x)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact e.symm_apply_apply x)

/-- A commuting linear equivalence induces an equivalence of cokernels. -/
noncomputable def cokerEquiv
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (e : M ≃ₗ[R] N) (h : dN.comp e.toLinearMap = e.toLinearMap.comp dM) :
    (M ⧸ dM.range) ≃ₗ[R] (N ⧸ dN.range) :=
  LinearEquiv.ofLinearMap
    (mapCoker dM dN e.toLinearMap h)
    (mapCoker dN dM e.symm.toLinearMap (equiv_symm_comm dM dN e h))
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective dN.range x
      change dN.range.mkQ (e (e.symm x)) = dN.range.mkQ x
      rw [e.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective dM.range x
      change dM.range.mkQ (e.symm (e x)) = dM.range.mkQ x
      rw [e.symm_apply_apply])

/-- In a short exact sequence with compatible endomorphisms, the induced
kernel maps are exact at the middle kernel. -/
theorem exact_mapKer
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N) (dP : P →ₗ[R] P)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hfcomm : dN.comp f = f.comp dM)
    (hgcomm : dP.comp g = g.comp dN) :
    Function.Exact (mapKer dM dN f hfcomm)
      (mapKer dN dP g hgcomm) := by
  intro y
  constructor
  · intro hy
    have hgy : g y = 0 := by
      simpa only [mapKer_apply_coe, Submodule.coe_zero] using
        congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (hfg y).mp hgy
    have hdx : dM x = 0 := by
      apply hf
      have hcomm := congrArg (fun k : M →ₗ[R] N => k x) hfcomm
      rw [comp_apply, comp_apply, hx, y.property] at hcomm
      exact hcomm.symm.trans f.map_zero.symm
    refine ⟨⟨x, hdx⟩, ?_⟩
    apply Subtype.ext
    simpa only [mapKer_apply_coe] using hx
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    simpa only [mapKer_apply_coe, Submodule.coe_zero] using
      hfg.apply_apply_eq_zero x

/-- In a short exact sequence with compatible endomorphisms, the induced
cokernel maps are exact at the middle cokernel. -/
theorem exact_mapCoker
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N) (dP : P →ₗ[R] P)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hfcomm : dN.comp f = f.comp dM)
    (hgcomm : dP.comp g = g.comp dN) :
    Function.Exact (mapCoker dM dN f hfcomm)
      (mapCoker dN dP g hgcomm) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective dN.range y
  constructor
  · intro hy
    change dP.range.mkQ (g y) = 0 at hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨x, rfl⟩ := hg z
    have hker : y - dN x ∈ ker g := by
      rw [mem_ker, map_sub, ← comp_apply, ← hgcomm, comp_apply, hz,
        sub_self]
    obtain ⟨a, ha⟩ := (hfg (y - dN x)).mp hker
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    change dN.range.mkQ (f a) = dN.range.mkQ y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    refine ⟨-x, ?_⟩
    rw [map_neg, ha]
    abel
  · rintro ⟨x, hx⟩
    rw [← hx]
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective dM.range x
    change dP.range.mkQ (g (f x)) = 0
    rw [hfg.apply_apply_eq_zero, map_zero]

end LinearMap
