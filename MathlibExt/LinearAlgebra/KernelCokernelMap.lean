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
# Kernels and cokernels of compatible endomorphisms

Let R be commutative and d_M,d_N endomorphisms of R-modules. A linear map f : M → N with d_N ∘
f = f ∘ d_M restricts to Ker(d_M) → Ker(d_N) and descends to M/Im(d_M) → N/Im(d_N). The
induced maps send x to f(x) and the class of x to the class of f(x). An injective f gives an
injective kernel map, a surjective f gives a surjective cokernel map, and a compatible linear
equivalence gives equivalences of both.

For an exact pair M → N → P with compatible endomorphisms, injectivity of its first map makes
the induced kernel pair exact at Ker(d_N). Surjectivity of its second map makes the induced
cokernel pair exact at N/Im(d_N). The scalar and three module universes are independent.
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

/-- Kernel map induced by commuting endomorphisms.

Over a commutative ring R, suppose d_N ∘ f = f ∘ d_M for f : M →ₗ[R] N. Restricting f to
Ker(d_M) gives a linear map to Ker(d_N), since d_N(f(x)) = f(d_M(x)) = 0. -/
def mapKer (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) :
    dM.ker →ₗ[R] dN.ker :=
  (f.comp dM.ker.subtype).codRestrict dN.ker fun x => by
    rw [mem_ker]
    have hx : dN (f x) = f (dM x) := by
      simpa only [comp_apply] using
        congrArg (fun k : M →ₗ[R] N => k x) h
    exact hx.trans <| (congrArg f (mem_ker.mp x.property)).trans f.map_zero

/-- Underlying value of an induced kernel map.

For a commuting square d_N ∘ f = f ∘ d_M and x ∈ Ker(d_M), the value of mapKer d_M d_N f,
viewed in N, is f(x). -/
@[simp]
theorem mapKer_apply_coe
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (x : dM.ker) :
    (mapKer dM dN f h x : N) = f x :=
  rfl

/-- Cokernel map induced by commuting endomorphisms.

For d_N ∘ f = f ∘ d_M over a commutative ring R, f maps Im(d_M) into Im(d_N). It therefore
induces a linear map M/Im(d_M) → N/Im(d_N) on the range-quotient cokernels. -/
def mapCoker (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) :
    (M ⧸ dM.range) →ₗ[R] (N ⧸ dN.range) :=
  dM.range.mapQ dN.range f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, congrArg (fun k : M →ₗ[R] N => k x) h⟩)

/-- Representative formula for an induced cokernel map.

For compatible d_M,d_N and f : M →ₗ[R] N, the induced cokernel map sends the class of x in
M/Im(d_M) to the class of f(x) in N/Im(d_N). -/
@[simp]
theorem mapCoker_mk
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM) (x : M) :
    mapCoker dM dN f h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  rfl

/-- Injectivity of a kernel map induced by an injective map.

If f : M →ₗ[R] N is injective and satisfies d_N ∘ f = f ∘ d_M, its restriction Ker(d_M) →
Ker(d_N) is injective. -/
theorem mapKer_injective
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (hf : Function.Injective f) :
    Function.Injective (mapKer dM dN f h) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  simpa only [mapKer_apply_coe] using congrArg Subtype.val hxy

/-- Surjectivity of a cokernel map induced by a surjective map.

If f : M →ₗ[R] N is surjective and satisfies d_N ∘ f = f ∘ d_M, the induced map M/Im(d_M) →
N/Im(d_N) is surjective. -/
theorem mapCoker_surjective
    (dM : M →ₗ[R] M) (dN : N →ₗ[R] N)
    (f : M →ₗ[R] N) (h : dN.comp f = f.comp dM)
    (hf : Function.Surjective f) :
    Function.Surjective (mapCoker dM dN f h) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective dN.range y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, mapCoker_mk dM dN f h x⟩

/-- Commuting square for the inverse of a linear equivalence.

If a linear equivalence e : M ≃ₗ[R] N satisfies d_N ∘ e = e ∘ d_M, then d_M ∘ e⁻¹ = e⁻¹ ∘ d_N.
Thus the inverse also intertwines the given endomorphisms. -/
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

/-- Kernel equivalence induced by a compatible linear equivalence.

For e : M ≃ₗ[R] N satisfying d_N ∘ e = e ∘ d_M, the restrictions of e and e⁻¹ give inverse
linear maps between Ker(d_M) and Ker(d_N). -/
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

/-- Cokernel equivalence induced by a compatible linear equivalence.

For a linear equivalence e intertwining d_M and d_N, the quotient maps induced by e and e⁻¹
are inverse. They define M/Im(d_M) ≃ₗ[R] N/Im(d_N). -/
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

/-- Exactness of induced kernels for an injective exact pair.

Let f : M → N and g : N → P be R-linear, with Im(f) = Ker(g), f injective and both maps
commuting with endomorphisms d_M,d_N,d_P. The induced pair Ker(d_M) → Ker(d_N) → Ker(d_P) is
exact at the middle kernel. Surjectivity of g is not part of this statement. -/
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

/-- Exactness of induced cokernels for a surjective exact pair.

Let f : M → N and g : N → P be R-linear, with Im(f) = Ker(g), g surjective and both maps
commuting with d_M,d_N,d_P. The induced pair M/Im(d_M) → N/Im(d_N) → P/Im(d_P) is exact at its
middle cokernel. The conclusion uses surjectivity of g to lift a range element of d_P. -/
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
