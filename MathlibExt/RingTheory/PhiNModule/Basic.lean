/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# `(φ, N)`-modules

Let `K₀` be a field, `σ` a ring automorphism of `K₀` (given, as for semilinear equivalences, with
its inverse `σ'`) and `p ∈ K₀`. A `(φ, N)`-module over `K₀` is a `K₀`-vector space `D` with a
bijective `σ`-semilinear map `φ : D → D` and a `K₀`-linear map `N : D → D` such that
`N (φ x) = p • φ (N x)` for all `x`. In the setting of Fontaine–Ouyang, `K₀ = W(k)[1/p]` is the
fraction field of the ring of Witt vectors of a perfect field `k` of characteristic `p`, `σ` is the
absolute Frobenius of `K₀`, `p` is the prime and `D` is finite-dimensional.

## Main definitions

* `PhiNModule σ p D`: a `(φ, N)`-module structure on the `K₀`-module `D`.
* `PhiNModule.IsStable`: a subspace stable under `φ` and `N`, that is, a sub-object.
* `PhiNModule.restrict` and `PhiNModule.quotient`: the `(φ, N)`-module structures on a stable
  subspace of a finite-dimensional `(φ, N)`-module and on the quotient by it.
* `PhiNModule.Hom`: morphisms, the `K₀`-linear maps commuting with `φ` and `N`.
* `PhiNModule.ofPhi`: the `(φ, N)`-module with `N = 0` attached to a `φ`-module.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.1, Definitions 8.13 and 8.14.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.2.1 p. 145.
-/

@[expose] public section

open Module

variable {K₀ : Type*} [Field K₀] (σ : K₀ →+* K₀) {σ' : K₀ →+* K₀} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] (p : K₀)

/-- A `(φ, N)`-module structure on a `K₀`-module `D`, for a ring automorphism `σ` of the field
`K₀` (with inverse `σ'`) and a scalar `p ∈ K₀`: a bijective `σ`-semilinear map `φ : D → D` (a
`σ`-semilinear equivalence) and a `K₀`-linear map `N : D → D` with `N (φ x) = p • φ (N x)` for all
`x : D`.

Fontaine–Ouyang (Definition 8.13) also require `D` to be finite-dimensional; here that is a
separate hypothesis `[FiniteDimensional K₀ D]` wherever it is used. -/
structure PhiNModule (D : Type*) [AddCommGroup D] [Module K₀ D] where
  /-- The Frobenius `φ : D → D`, a bijective `σ`-semilinear map. -/
  φ : D ≃ₛₗ[σ] D
  /-- The monodromy operator `N : D → D`, a `K₀`-linear map. -/
  N : D →ₗ[K₀] D
  /-- The relation `N φ = p φ N`. -/
  N_φ (x : D) : N (φ x) = p • φ (N x)

namespace PhiNModule

variable {σ p} {D : Type*} [AddCommGroup D] [Module K₀ D] (M : PhiNModule σ p D)

/-- The `(φ, N)`-module with monodromy `N = 0` attached to a bijective `σ`-semilinear map
`φ : D → D`; the `(φ, N)`-modules with `N = 0` are the `φ`-modules of Fontaine–Ouyang,
Definition 8.14. -/
def ofPhi (φ : D ≃ₛₗ[σ] D) : PhiNModule σ p D where
  φ := φ
  N := 0
  N_φ x := by simp

/-- The Frobenius of `PhiNModule.ofPhi φ` is `φ`. -/
@[simp]
theorem ofPhi_φ (φ : D ≃ₛₗ[σ] D) : (ofPhi (p := p) φ).φ = φ := rfl

/-- The monodromy operator of `PhiNModule.ofPhi φ` is `0`. -/
@[simp]
theorem ofPhi_N (φ : D ≃ₛₗ[σ] D) : (ofPhi (p := p) φ).N = 0 := rfl

/-! ### Stable subspaces -/

/-- A subspace `D'` of a `(φ, N)`-module is *stable* if `φ` and `N` map `D'` into itself. These
are the sub-objects of Fontaine–Ouyang, Definition 8.39 (ii). -/
structure IsStable (D' : Submodule K₀ D) : Prop where
  /-- `φ` maps `D'` into itself. -/
  φ_mem {x : D} : x ∈ D' → M.φ x ∈ D'
  /-- `N` maps `D'` into itself. -/
  N_mem {x : D} : x ∈ D' → M.N x ∈ D'

variable {M}

/-- The zero subspace is stable. -/
theorem isStable_bot : M.IsStable ⊥ where
  φ_mem hx := by simp_all
  N_mem hx := by simp_all

/-- The whole space is stable. -/
theorem isStable_top : M.IsStable ⊤ where
  φ_mem _ := Submodule.mem_top
  N_mem _ := Submodule.mem_top

/-- A `σ`-semilinear equivalence preserves the dimension of subspaces. -/
private theorem finrank_map_semilinearEquiv (e : D ≃ₛₗ[σ] D) (D' : Submodule K₀ D) :
    finrank K₀ (D'.map (e : D →ₛₗ[σ] D)) = finrank K₀ D' := by
  have hσ : Function.Bijective σ := Function.bijective_iff_has_inverse.mpr
    ⟨σ', fun _ => RingHomInvPair.comp_apply_eq, fun _ => RingHomInvPair.comp_apply_eq₂⟩
  have := rank_eq_of_equiv_equiv σ (e.submoduleMap D').toAddEquiv hσ fun r m =>
    LinearEquiv.map_smulₛₗ (e.submoduleMap D') r m
  simp only [Module.finrank, this]

/-- In a finite-dimensional `(φ, N)`-module, `φ` maps a stable subspace onto itself. -/
theorem IsStable.map_φ_eq [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D') :
    D'.map (M.φ : D →ₛₗ[σ] D) = D' := by
  refine Submodule.eq_of_le_of_finrank_le ?_ (finrank_map_semilinearEquiv M.φ D').ge
  rintro - ⟨x, hx, rfl⟩
  exact h.φ_mem hx

/-- In a finite-dimensional `(φ, N)`-module, every vector of a stable subspace `D'` is the image
under `φ` of a vector of `D'`. -/
theorem IsStable.exists_φ_eq [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D')
    {y : D} (hy : y ∈ D') : ∃ x ∈ D', M.φ x = y := by
  rw [← h.map_φ_eq] at hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨x, hx, rfl⟩

/-- In a finite-dimensional `(φ, N)`-module, a vector whose image under `φ` lies in a stable
subspace `D'` lies in `D'`. -/
theorem IsStable.mem_of_φ_mem [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D')
    {x : D} (hx : M.φ x ∈ D') : x ∈ D' := by
  obtain ⟨y, hy, hxy⟩ := h.exists_φ_eq hx
  rwa [M.φ.injective hxy] at hy

variable (M)

/-! ### Restriction to a stable subspace and quotient -/

/-- The `(φ, N)`-module structure on a stable subspace `D'` of a finite-dimensional
`(φ, N)`-module `D`, by the restrictions of `φ` and `N`. -/
noncomputable def restrict [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') :
    PhiNModule σ p D' where
  φ := LinearEquiv.ofBijective ((M.φ : D →ₛₗ[σ] D).restrict fun _ hx => h.φ_mem hx)
    ⟨fun x y hxy => Subtype.ext (M.φ.injective (congrArg Subtype.val hxy)), fun y => by
      obtain ⟨x, hx, hxy⟩ := h.exists_φ_eq y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  N := M.N.restrict fun _ hx => h.N_mem hx
  N_φ x := Subtype.ext (M.N_φ x)

/-- The Frobenius of the restriction of a finite-dimensional `(φ, N)`-module to a stable
subspace `D'` is the restriction of `φ`: for `x ∈ D'`, it sends `x` to `φ x`. -/
@[simp]
theorem coe_restrict_φ_apply [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D')
    (x : D') : ((M.restrict D' h).φ x : D) = M.φ x := rfl

/-- The monodromy operator of the restriction of a finite-dimensional `(φ, N)`-module to a stable
subspace `D'` is the restriction of `N`: for `x ∈ D'`, it sends `x` to `N x`. -/
@[simp]
theorem coe_restrict_N_apply [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D')
    (x : D') : ((M.restrict D' h).N x : D) = M.N x := rfl

/-- The quotient `(φ, N)`-module `D ⧸ D'` of a finite-dimensional `(φ, N)`-module `D` by a stable
subspace `D'`, with the maps induced by `φ` and `N`. -/
noncomputable def quotient [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') :
    PhiNModule σ p (D ⧸ D') where
  φ := LinearEquiv.ofBijective (D'.mapQ D' (M.φ : D →ₛₗ[σ] D) fun _ hx => h.φ_mem hx)
    ⟨by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        exact h.mem_of_φ_mem hx,
    fun y => by
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨x, rfl⟩ := M.φ.surjective y
        exact ⟨Submodule.Quotient.mk x, rfl⟩⟩
  N := D'.mapQ D' M.N fun _ hx => h.N_mem hx
  N_φ x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (M.N (M.φ x)) = p • Submodule.Quotient.mk (M.φ (M.N x))
      rw [M.N_φ, Submodule.Quotient.mk_smul]

/-- The Frobenius of the quotient of a finite-dimensional `(φ, N)`-module by a stable subspace
`D'` sends the class of `x` to the class of `φ x`. -/
@[simp]
theorem quotient_φ_mk [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') (x : D) :
    (M.quotient D' h).φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (M.φ x) := rfl

/-- The monodromy operator of the quotient of a finite-dimensional `(φ, N)`-module by a stable
subspace `D'` sends the class of `x` to the class of `N x`. -/
@[simp]
theorem quotient_N_mk [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') (x : D) :
    (M.quotient D' h).N (Submodule.Quotient.mk x) = Submodule.Quotient.mk (M.N x) := rfl

variable {M}

/-- A stable subspace of the restriction of `D` to a stable subspace `D'` is, viewed in `D`, a
stable subspace of `D`. -/
theorem IsStable.map_subtype [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D')
    {D'' : Submodule K₀ D'} (h' : (M.restrict D' h).IsStable D'') :
    M.IsStable (D''.map D'.subtype) where
  φ_mem := by
    rintro - ⟨x, hx, rfl⟩
    exact ⟨_, h'.φ_mem hx, rfl⟩
  N_mem := by
    rintro - ⟨x, hx, rfl⟩
    exact ⟨_, h'.N_mem hx, rfl⟩

/-- The preimage in `D` of a stable subspace of the quotient of `D` by a stable subspace `D'` is a
stable subspace of `D`. -/
theorem IsStable.comap_mkQ [FiniteDimensional K₀ D] {D' : Submodule K₀ D} (h : M.IsStable D')
    {C : Submodule K₀ (D ⧸ D')} (hC : (M.quotient D' h).IsStable C) :
    M.IsStable (C.comap D'.mkQ) where
  φ_mem {x} hx := hC.φ_mem (x := Submodule.Quotient.mk x) hx
  N_mem {x} hx := hC.N_mem (x := Submodule.Quotient.mk x) hx

/-! ### Morphisms -/

variable {D₁ D₂ : Type*} [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂]

/-- A morphism of `(φ, N)`-modules `M₁ → M₂`: a `K₀`-linear map commuting with `φ` and with `N`
(Fontaine–Ouyang, Definition 8.13 (ii)). -/
structure Hom (M₁ : PhiNModule σ p D₁) (M₂ : PhiNModule σ p D₂) where
  /-- The underlying `K₀`-linear map. -/
  toLinearMap : D₁ →ₗ[K₀] D₂
  /-- The map commutes with `φ`. -/
  map_φ (x : D₁) : toLinearMap (M₁.φ x) = M₂.φ (toLinearMap x)
  /-- The map commutes with `N`. -/
  map_N (x : D₁) : toLinearMap (M₁.N x) = M₂.N (toLinearMap x)

variable {M₁ : PhiNModule σ p D₁} {M₂ : PhiNModule σ p D₂}

/-- The kernel of a morphism of `(φ, N)`-modules is a stable subspace of its source. -/
theorem Hom.isStable_ker (f : M₁.Hom M₂) : M₁.IsStable (LinearMap.ker f.toLinearMap) where
  φ_mem {x} hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.map_φ, hx, map_zero]
  N_mem {x} hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.map_N, hx, map_zero]

/-- The image of a morphism of `(φ, N)`-modules is a stable subspace of its target. -/
theorem Hom.isStable_range (f : M₁.Hom M₂) : M₂.IsStable (LinearMap.range f.toLinearMap) where
  φ_mem := by
    rintro - ⟨x, rfl⟩
    exact ⟨M₁.φ x, f.map_φ x⟩
  N_mem := by
    rintro - ⟨x, rfl⟩
    exact ⟨M₁.N x, f.map_N x⟩

end PhiNModule
