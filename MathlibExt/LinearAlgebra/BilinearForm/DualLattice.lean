/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

open scoped nonZeroDivisors

open Submodule

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]

/-- If `M` spans `V` over the fraction field, its subtype is a localized module map. -/
theorem Submodule.isLocalizedModule_subtype_of_span_eq_top (M : Submodule A V)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    IsLocalizedModule (A⁰) M.subtype where
  map_units s := by
    rw [← (Algebra.lsmul A (A := K) A V).commutes]
    exact (IsLocalization.map_units K s).map _
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set V) := hspan ▸ trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      exact ⟨⟨⟨x, hx⟩, 1⟩, by simp⟩
    | zero =>
      exact ⟨⟨0, 1⟩, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨⟨a, s⟩, hs⟩ := hx
      obtain ⟨⟨b, t⟩, ht⟩ := hz
      refine ⟨⟨t • a + s • b, s * t⟩, ?_⟩
      simp only [Submonoid.smul_def] at hs ht ⊢
      change ((s * t : A⁰) : A) • (x + z) = ↑(t • a + s • b)
      simp only [Submonoid.coe_mul]
      rw [smul_add]
      change ((s : A) * (t : A)) • x + ((s : A) * (t : A)) • z =
        (t : A) • ((a : M) : V) + (s : A) • ((b : M) : V)
      congr 1
      · rw [mul_comm, mul_smul, hs]
        rfl
      · rw [mul_smul, ht]
        rfl
    | smul c x _ hx =>
      obtain ⟨⟨a, s⟩, hs⟩ := hx
      obtain ⟨⟨r, d⟩, hd⟩ := IsLocalization.surj (A⁰) c
      refine ⟨⟨r • a, s * d⟩, ?_⟩
      simp only [Submonoid.smul_def] at hs ⊢
      have hdc : algebraMap A K (d : A) * c = algebraMap A K r := by
        simpa [mul_comm] using hd
      change ((s * d : A⁰) : A) • (c • x) = (r : A) • ((a : M) : V)
      rw [← IsScalarTower.algebraMap_smul K] at hs ⊢
      simp only [Submonoid.coe_mul, map_mul, smul_smul] at hs ⊢
      rw [mul_assoc, hdc, mul_comm (algebraMap A K (s : A)) _, mul_smul, hs]
      rw [IsScalarTower.algebraMap_smul]
      rfl
  exists_of_eq h := ⟨1, by simpa [Submonoid.smul_def] using h⟩

/-- The pairing map from the dual submodule onto the module dual is surjective. -/
theorem LinearMap.BilinForm.dualSubmoduleToDual_surjective [IsDomain A]
    [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual M) := by
  let _ : IsLocalizedModule A⁰ M.subtype :=
    Submodule.isLocalizedModule_subtype_of_span_eq_top M hspan
  intro f
  let fK : V →ₗ[K] K :=
    IsLocalizedModule.mapExtendScalars A⁰ M.subtype (Algebra.linearMap A K) K f
  set x := (B.toDual hB).symm fK with hx
  have key : ∀ y : M, B x (y : V) = algebraMap A K (f y) := fun y => by
    rw [hx, LinearMap.BilinForm.apply_toDual_symm_apply]
    change (IsLocalizedModule.map A⁰ M.subtype (Algebra.linearMap A K) f) (M.subtype y) =
      algebraMap A K (f y)
    simpa using IsLocalizedModule.map_apply A⁰ M.subtype (Algebra.linearMap A K) f y
  have hmem : x ∈ B.dualSubmodule M := fun y hy =>
    Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, by simpa using (key ⟨y, hy⟩).symm⟩
  refine ⟨⟨x, hmem⟩, ?_⟩
  ext y
  apply FaithfulSMul.algebraMap_injective A K
  change algebraMap A K (B.dualSubmodulePairing ⟨x, hmem⟩ y) = algebraMap A K (f y)
  rw [LinearMap.BilinForm.dualSubmodulePairing_spec, key y]

/-- The pairing map from the dual submodule to the module dual is bijective. -/
theorem LinearMap.BilinForm.dualSubmoduleToDual_bijective [IsDomain A]
    [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    Function.Bijective (B.dualSubmoduleToDual M) :=
  ⟨B.dualSubmoduleToDual_injective hB M hspan,
    B.dualSubmoduleToDual_surjective hB M hspan⟩

/-- The dual submodule of a lattice is finitely generated. -/
theorem LinearMap.BilinForm.dualSubmodule_fg [IsDomain A] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    [Module.Finite A M]
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    (B.dualSubmodule M).FG := by
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.of_injective (B.dualSubmoduleToDual M)
    (B.dualSubmoduleToDual_injective hB M hspan)

/-- The dual submodule spans the whole space over the fraction field. -/
theorem LinearMap.BilinForm.dualSubmodule_span_eq_top
    (B : LinearMap.BilinForm K V) (M : Submodule A V) (hfg : M.FG) :
    Submodule.span K (B.dualSubmodule M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples A⁰ s (fun y => B x y)
  have hBsmul : ∀ y, B ((d : A) • x) y = (d : A) • B x y := fun y => by
    rw [← IsScalarTower.algebraMap_smul K]
    rw [map_smul, LinearMap.smul_apply, IsScalarTower.algebraMap_smul K]
  have hle : M ≤
      (1 : Submodule A K).comap ((B ((d : A) • x)).restrictScalars A) := by
    rw [← hs, Submodule.span_le]
    intro y hy
    change B ((d : A) • x) y ∈ (1 : Submodule A K)
    obtain ⟨a, ha⟩ := hd y (Finset.mem_coe.mp hy)
    exact Submodule.mem_one.mpr ⟨a, by simpa using ha.trans (hBsmul y).symm⟩
  have hmem : (d : A) • x ∈ B.dualSubmodule M := fun y hy => hle hy
  have hspanmem : (d : A) • x ∈ Submodule.span K (B.dualSubmodule M : Set V) :=
    Submodule.subset_span hmem
  obtain ⟨u, hu⟩ := IsLocalization.map_units K d
  have hdx : (d : A) • x = (u : K) • x := by
    rw [hu, IsScalarTower.algebraMap_smul K]
  have hx : x = ((u⁻¹ : Kˣ) : K) • ((d : A) • x) := by
    rw [hdx, ← mul_smul, Units.inv_mul, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hspanmem

/-- The dual submodule of a lattice is a lattice. -/
theorem LinearMap.BilinForm.dualSubmodule_isLattice [IsDomain A] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    [Submodule.IsLattice K M] : Submodule.IsLattice K (B.dualSubmodule M) where
  fg := B.dualSubmodule_fg hB M IsLattice.span_eq_top
  span_eq_top := B.dualSubmodule_span_eq_top M IsLattice.fg

/-- Combined endpoint: the dual submodule is a lattice and dual map is bijective. -/
theorem LinearMap.BilinForm.dualSubmodule_isLattice_and_dualSubmoduleToDual_bijective
    [IsDomain A] [FiniteDimensional K V] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    [Submodule.IsLattice K M] :
    Submodule.IsLattice K (B.dualSubmodule M) ∧
      Function.Bijective (B.dualSubmoduleToDual M) :=
  ⟨B.dualSubmodule_isLattice hB M,
    B.dualSubmoduleToDual_bijective hB M IsLattice.span_eq_top⟩

/-- The canonical equivalence induced by the bilinear pairing. -/
noncomputable def LinearMap.BilinForm.dualSubmoduleLinearEquiv
    [IsDomain A] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    (B.dualSubmodule M) ≃ₗ[A] Module.Dual A M :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual M)
    (B.dualSubmoduleToDual_bijective hB M hspan)
