/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Filtration

/-! Tests for filtered rings of periods: `Fil^i D_S(V)` is a decreasing filtration of `D_S(V)`, the
class of `x` in `gr^i D_S(V)` vanishes exactly on `Fil^{i+1} D_S(V)`, a map vanishing exactly on
`Fil^{i+1} D_S(V)` induces an injection of `gr^i D_S(V)`, the filtration passes exhaustiveness
and separatedness to `S ⊗ V`, and over a regular ring the filtration of `D_S(V)` is finite with
`dim D_S(V) = Σᵢ dim gr^i D_S(V)`. -/

open scoped TensorProduct

open Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

-- `Fil^i D_S(V)` lies in `D_S(V)` and decreases with `i`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (fil : ℤ → Submodule F S)
    (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i)
    (hanti : Antitone fil) {i j : ℤ} (hij : i ≤ j) {x : S ⊗[F] V}
    (hx : x ∈ ρ.periodsFiltration act H fil hfil j) :
    x ∈ ρ.periods act H ∧ x ∈ ρ.periodsFiltration act H fil hfil i :=
  ⟨ρ.periodsFiltration_le_periods act H fil hfil j hx,
    ρ.periodsFiltration_antitone act H fil hfil hanti hij hx⟩

-- The class of `x ∈ Fil^i D_S(V)` in `gr^i D_S(V)` vanishes exactly for `x ∈ Fil^{i+1} D_S(V)`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (fil : ℤ → Submodule F S)
    (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i) {i : ℤ}
    (x : ρ.periodsFiltration act H fil hfil i) :
    ρ.periodsGradedMk act H fil hfil i x = 0 ↔
      (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1) :=
  ρ.periodsGradedMk_eq_zero_iff act H fil hfil x

-- A map on `Fil^i D_S(V)` with kernel `Fil^{i+1} D_S(V)` induces an injection of `gr^i D_S(V)`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (fil : ℤ → Submodule F S)
    (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i) {i : ℤ}
    {W : Type*} [AddCommGroup W] [Module F W] (f : ρ.periodsFiltration act H fil hfil i →ₗ[F] W)
    (hf : ∀ x, f x = 0 ↔ (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1)) :
    Function.Injective (ρ.periodsGradedLift act H fil hfil f fun x hx => (hf x).2 hx) :=
  periodsGradedLift_injective f _ fun x => (hf x).1

-- Exhaustiveness and separatedness of the filtration of `S` pass to `S ⊗ V`.
example (fil : ℤ → Submodule F S) (hanti : Antitone fil) (hexh : ∀ s : S, ∃ i, s ∈ fil i)
    (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) (z : S ⊗[F] V) :
    (∃ i, z ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype)) ∧
      ((∀ i, z ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype)) → z = 0) :=
  ⟨exists_mem_range_rTensor hanti hexh z, eq_zero_of_forall_mem_range_rTensor hsep⟩

-- Over a regular ring, the filtration of `D_S(V)` is finite and
-- `dim_{S^H} D_S(V) = Σᵢ dim_{S^H} gr^i D_S(V)`.
example [IsDomain S] (act : G →* (S →ₐ[F] S)) (H : Subgroup G) (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] [Module.Finite F (fixedSubalgebra S act H)]
    (fil : ℤ → Submodule F S)
    (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i)
    (hanti : Antitone fil) (hexh : ∀ s : S, ∃ i, s ∈ fil i)
    (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) :
    (∃ a, ∀ i ≤ a, ρ.periodsFiltration act H fil hfil i = ρ.periods act H) ∧
      (∃ b, ∀ i, b ≤ i → ρ.periodsFiltration act H fil hfil i = ⊥) ∧
      Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) =
        ∑ᶠ i, Module.finrank (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) :=
  ⟨ρ.exists_periodsFiltration_eq_periods hS hfil hanti hexh,
    ρ.exists_periodsFiltration_eq_bot hS hfil hanti hsep,
    ρ.finrank_periods_eq_finsum_finrank_periodsGraded hS hfil hanti hexh hsep⟩

-- Over a regular ring, a nonzero invariant gives `dim_{S^H} D_S(V) ≥ 1`.
example [IsDomain S] (act : G →* (S →ₐ[F] S)) (H : Subgroup G) (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] {x : S ⊗[F] V}
    (hx : x ∈ ρ.periods act H) (hx0 : x ≠ 0) :
    1 ≤ Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) :=
  ρ.one_le_finrank_periods hS hx hx0
