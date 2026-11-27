/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.DeRhamFiltration

/-!
# Tests for the filtrations of `B_dR` and `D_dR(V)`

`t = log [ε]` is a uniformizer of `B_dR^+` on which `σ` acts by `χ(σ)`; `t^i ∈ Fil^j B_dR`
exactly for `j ≤ i`; `Fil^0 B_dR = B_dR^+`, the filtration is multiplicative, exhaustive and
separated; `gr^i B_dR ≅ ℂ_p(i)` intertwines the actions; `B_dR^{G_K} ≅ K`; the filtration of
`D_dR(V)` lies in `D_dR(V)` and decreases; and `gr^i D_dR(V)` embeds in
`(ℂ_p(i) ⊗ V)^{G_K}`.
-/

open MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplexInt Representation
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝕥" => logTeichmuller p (untilt_epsilon p)

/-- `t = log [ε]` is a uniformizer of `B_dR^+`, and `σ(t) = χ(σ) t`. -/
example (σ : Galois p) :
    Irreducible 𝕥 ∧ galoisBDeRhamPlus p σ 𝕥 = cyclotomicScalar p σ • 𝕥 :=
  ⟨irreducible_logTeichmuller_epsilon p, galoisBDeRhamPlus_logTeichmuller_epsilon p σ⟩

/-- `Fil^j B_dR = t^j B_dR^+` contains `t^i` exactly when `j ≤ i`. -/
example (i j : ℤ) : algebraMap 𝔹⁺ 𝔹 𝕥 ^ i ∈ filBDeRham p j ↔ j ≤ i := by
  simpa using units_mul_zpow_mem_filBDeRham_iff p 1 (n := i) (i := j)

/-- `Fil^0 B_dR = B_dR^+`, `Fil^{i+j} B_dR = Fil^i B_dR · Fil^j B_dR`, and the filtration is
exhaustive and separated. -/
example (i j : ℤ) :
    filBDeRham p 0 = 1 ∧ filBDeRham p (i + j) = filBDeRham p i * filBDeRham p j ∧
      ⨆ i, filBDeRham p i = ⊤ ∧ ⨅ i, filBDeRham p i = ⊥ :=
  ⟨filBDeRham_zero p, filBDeRham_add p i j, iSup_filBDeRham p, iInf_filBDeRham p⟩

/-- `gr^i B_dR ≅ ℂ_p(i)`: the class of `x ∈ Fil^i B_dR` goes to `θ(t^{-i} x)`, and `σ x` goes to
`χ(σ)ⁱ σ(θ(t^{-i} x))`. -/
example (i : ℤ) (σ : Galois p) (x : (filBDeRham p i).restrictScalars ℚ_[p]) :
    grBDeRhamEquiv p i (Submodule.Quotient.mk (filBDeRhamRepresentation p i σ x)) =
      cyclotomicScalar p σ ^ i •
        completionGalois p σ (grBDeRhamEquiv p i (Submodule.Quotient.mk x)) := by
  rw [grBDeRhamEquiv_mk, grBDeRhamEquiv_mk, filBDeRhamTheta_filBDeRhamRepresentation]

/-- `B_dR^{G_K} ≅ K` through `K ⊆ ℚ̄_p ⊆ B_dR^+ ⊆ B_dR`, for `K` finite over `ℚ_p`. -/
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (y : K) :
    (deRhamFixedSubalgebraEquiv p K y : 𝔹) = algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) :=
  coe_deRhamFixedSubalgebraEquiv p K y

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `Fil^j D_dR(V)` consists of the elements of `D_dR(V)` in `Fil^j B_dR ⊗ V`, and lies in
`Fil^i D_dR(V)` for `i ≤ j`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {i j : ℤ} (hij : i ≤ j) {x : 𝔹 ⊗[ℚ_[p]] V}
    (hx : x ∈ ρ.deRhamFiltration K j) :
    x ∈ ρ.periods (galoisBDeRham p) K.fixingSubgroup ∧ x ∈ filBDeRhamTensor p V j ∧
      x ∈ ρ.deRhamFiltration K i :=
  ⟨((mem_deRhamFiltration ρ K).1 hx).1, ((mem_deRhamFiltration ρ K).1 hx).2,
    deRhamFiltration_antitone ρ K hij hx⟩

/-- `gr^i D_dR(V)` embeds in `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`, the class of `x` going to
`(θᵢ ⊗ V)(x)`. -/
example (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (i : ℤ) (x : ρ.deRhamFiltration K i) :
    Function.Injective (deRhamGradedToTwistPeriods ρ K i) ∧
      (deRhamGradedToTwistPeriods ρ K i (ρ.periodsGradedMk _ _ _ _ i x) :
        ℂ_[p] ⊗[ℚ_[p]] V) = filBDeRhamTensorTheta p V i ⟨x, x.2.2⟩ :=
  ⟨deRhamGradedToTwistPeriods_injective ρ K i, rfl⟩
