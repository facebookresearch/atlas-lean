/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.DecreasingFiltration
public import MathlibExt.RingTheory.PhiNModule.NewtonNumber
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Weakly admissible filtered `(φ, N)`-modules

Let `K₀` be a field with a ring automorphism `σ`, let `p ∈ K₀`, and let `K` be a field extension
of `K₀`. A *filtered `(φ, N)`-module* over `K` is a `(φ, N)`-module `D` over `K₀` together with a
decreasing, separated and exhaustive `ℤ`-indexed filtration of `D_K = K ⊗_{K₀} D` by
`K`-subspaces. If `D` is finite-dimensional, it has a Hodge number
`t_H(D) = ∑ᵢ i · dim_K gr^i D_K` and, for an additive valuation `v` of `K₀`, a Newton number
`t_N(D)` (`PhiNModule.newtonNumber`). The module `D` is *weakly admissible* if `t_H(D) = t_N(D)`
and `t_H(D') ≤ t_N(D')` for every subspace `D' ⊆ D` stable under `φ` and `N`, with the induced
filtration on `D'_K`.

In the setting of Fontaine–Ouyang, `K` is a `p`-adic field (complete, discretely valued, of
characteristic `0`, with perfect residue field `k` of characteristic `p`), `K₀ = W(k)[1/p]` is its
maximal absolutely unramified subfield, `σ` is the absolute Frobenius of `K₀`, `p` is the prime
and `v` is the `p`-adic valuation, normalized by `v(p) = 1`. The definitions and results here only
use a field extension `K` of `K₀` and an additive valuation `v` with `v ∘ σ = v`. Fontaine–Ouyang
call weakly admissible modules *admissible*; by their Remark 8.55, *weakly admissible* is the
older name, used by Fontaine (*faiblement admissible*). The weakly admissible filtered
`(φ, N)`-modules with `N = 0` (`PhiNModule.ofPhi`) are the weakly admissible filtered
`φ`-modules.

## Main definitions

* `FilteredPhiNModule σ p K D`: a filtered `(φ, N)`-module.
* `FilteredPhiNModule.restrict`, `FilteredPhiNModule.quotient`: a stable subspace with the
  induced filtration, and the quotient by it with the quotient filtration.
* `FilteredPhiNModule.hodgeNumber`: the Hodge number `t_H(D)`.
* `FilteredPhiNModule.IsWeaklyAdmissible`: weak admissibility.

## Main results

* `FilteredPhiNModule.hodgeNumber_eq_restrict_add_quotient`: additivity of `t_H`.
* `FilteredPhiNModule.isWeaklyAdmissible_iff_quotient`: the equivalent condition on quotients.
* `FilteredPhiNModule.isWeaklyAdmissible_iff_of_finrank_eq_one`: a one-dimensional module is
  weakly admissible if and only if `t_H(D) = t_N(D)`.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.3–§8.2.5: Definitions 8.34, 8.36 and 8.39, (8.11), Remark 8.40; Remark 8.55.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.3.2–§4.3.3 pp. 148–149 and §4.4.1–§4.4.3 pp. 150–151.
-/

@[expose] public section

open Module TensorProduct

section BaseChange

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module K₀ M₁] [AddCommGroup M₂] [Module K₀ M₂]
  [AddCommGroup M₃] [Module K₀ M₃]

/-- Extension of scalars along a field extension preserves injectivity. -/
private theorem baseChange_injective {f : M₁ →ₗ[K₀] M₂} (hf : Function.Injective f) :
    Function.Injective (f.baseChange K) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Extension of scalars preserves surjectivity. -/
private theorem baseChange_surjective {g : M₂ →ₗ[K₀] M₃} (hg : Function.Surjective g) :
    Function.Surjective (g.baseChange K) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_surjective K hg

/-- Extension of scalars preserves exactness at the middle of a right exact sequence. -/
private theorem baseChange_exact {f : M₁ →ₗ[K₀] M₂} {g : M₂ →ₗ[K₀] M₃}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.baseChange K) (g.baseChange K) := by
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
  exact lTensor_exact K hfg hg

end BaseChange

variable {K₀ : Type*} [Field K₀] (σ : K₀ →+* K₀) {σ' : K₀ →+* K₀} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] (p : K₀) (K : Type*) [Field K] [Algebra K₀ K]

/-- A filtered `(φ, N)`-module over `K` (Fontaine–Ouyang, Definition 8.34 (1); Fontaine,
Exposé III, §4.3.2), for a field `K₀` with a ring automorphism `σ` (with inverse `σ'`), a scalar
`p ∈ K₀` and a field extension `K` of `K₀`: a `(φ, N)`-module structure on the `K₀`-module `D`
together with a decreasing, separated and exhaustive `ℤ`-indexed filtration `(Fil^i D_K)_{i ∈ ℤ}`
of `D_K = K ⊗_{K₀} D` by `K`-subspaces. As for `PhiNModule`, the finite-dimensionality of `D`
over `K₀` required by Fontaine–Ouyang is a separate hypothesis wherever it is used. -/
structure FilteredPhiNModule (D : Type*) [AddCommGroup D] [Module K₀ D] extends
    PhiNModule σ p D where
  /-- The filtration `(Fil^i D_K)_{i ∈ ℤ}` of `D_K = K ⊗[K₀] D`. -/
  fil : DecreasingFiltration K (K ⊗[K₀] D)

namespace FilteredPhiNModule

variable {σ p K} {D : Type*} [AddCommGroup D] [Module K₀ D] (M : FilteredPhiNModule σ p K D)

/-- The Hodge number `t_H(D) = t_H(D_K) = ∑ᵢ i · dim_K gr^i D_K` of a filtered `(φ, N)`-module
(Fontaine–Ouyang, Definition 8.36 and (8.11)). -/
noncomputable def hodgeNumber : ℤ := M.fil.hodgeNumber

/-- The Hodge number of a filtered `(φ, N)`-module on a zero-dimensional space `D` is `0`. -/
theorem hodgeNumber_eq_zero_of_finrank_eq_zero [FiniteDimensional K₀ D]
    (hD : finrank K₀ D = 0) : M.hodgeNumber = 0 :=
  M.fil.hodgeNumber_eq_zero_of_finrank_eq_zero (by rw [Module.finrank_baseChange, hD])

/-! ### Sub-objects and quotients -/

/-- The filtered `(φ, N)`-module structure on a stable subspace `D'` of a finite-dimensional
filtered `(φ, N)`-module `D`: the restrictions of `φ` and `N`, and on `D'_K = K ⊗_{K₀} D'`,
identified with a subspace of `D_K`, the induced filtration `Fil^i D'_K = D'_K ∩ Fil^i D_K`.
These are the sub-objects of Fontaine–Ouyang, Definition 8.39 (ii). -/
noncomputable def restrict [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') :
    FilteredPhiNModule σ p K D' where
  toPhiNModule := M.toPhiNModule.restrict D' h
  fil := M.fil.comap (D'.subtype.baseChange K) <| by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ D'.injective_subtype

/-- The quotient filtered `(φ, N)`-module `D ⧸ D'` of a finite-dimensional filtered
`(φ, N)`-module `D` by a stable subspace `D'`: the maps induced by `φ` and `N`, and on
`(D ⧸ D')_K = K ⊗_{K₀} (D ⧸ D')` the quotient filtration, the image of `Fil^i D_K`. -/
noncomputable def quotient [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D') :
    FilteredPhiNModule σ p K (D ⧸ D') where
  toPhiNModule := M.toPhiNModule.quotient D' h
  fil := M.fil.map (D'.mkQ.baseChange K) <| by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective K D'.mkQ_surjective

/-- The `(φ, N)`-module underlying the restriction of a finite-dimensional filtered
`(φ, N)`-module to a stable subspace `D'` is the restriction of its underlying `(φ, N)`-module. -/
@[simp]
theorem restrict_toPhiNModule [FiniteDimensional K₀ D] (D' : Submodule K₀ D)
    (h : M.IsStable D') : (M.restrict D' h).toPhiNModule = M.toPhiNModule.restrict D' h :=
  rfl

/-- The `(φ, N)`-module underlying the quotient of a finite-dimensional filtered `(φ, N)`-module
by a stable subspace `D'` is the quotient of its underlying `(φ, N)`-module. -/
@[simp]
theorem quotient_toPhiNModule [FiniteDimensional K₀ D] (D' : Submodule K₀ D)
    (h : M.IsStable D') : (M.quotient D' h).toPhiNModule = M.toPhiNModule.quotient D' h :=
  rfl

/-- The `i`-th step of the filtration of the restriction to a stable subspace `D'` is the
preimage of `Fil^i D_K` under `K ⊗_{K₀} D' → D_K`. -/
theorem restrict_fil_fil [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D')
    (i : ℤ) : (M.restrict D' h).fil.Fil i = (M.fil.Fil i).comap (D'.subtype.baseChange K) :=
  rfl

/-- The `i`-th step of the filtration of the quotient by a stable subspace `D'` is the image of
`Fil^i D_K` under `D_K → K ⊗_{K₀} (D ⧸ D')`. -/
theorem quotient_fil_fil [FiniteDimensional K₀ D] (D' : Submodule K₀ D) (h : M.IsStable D')
    (i : ℤ) : (M.quotient D' h).fil.Fil i = (M.fil.Fil i).map (D'.mkQ.baseChange K) :=
  rfl

/-- Additivity of the Hodge number (Fontaine–Ouyang, Proposition 8.38 (1)): for a stable
subspace `D'` of a finite-dimensional filtered `(φ, N)`-module `D`, with the induced filtration
on `D'_K` and the quotient filtration on `(D ⧸ D')_K`, `t_H(D) = t_H(D') + t_H(D ⧸ D')`. -/
theorem hodgeNumber_eq_restrict_add_quotient [FiniteDimensional K₀ D] (D' : Submodule K₀ D)
    (h : M.IsStable D') :
    M.hodgeNumber = (M.restrict D' h).hodgeNumber + (M.quotient D' h).hodgeNumber :=
  M.fil.hodgeNumber_eq_add_of_exact (baseChange_injective D'.injective_subtype)
    (baseChange_surjective D'.mkQ_surjective)
    (baseChange_exact (LinearMap.exact_subtype_mkQ D') D'.mkQ_surjective)

/-! ### Weak admissibility -/

/-- A finite-dimensional filtered `(φ, N)`-module `D` is *weakly admissible*, for an additive
valuation `v` of `K₀`, if `t_H(D) = t_N(D)` and `t_H(D') ≤ t_N(D')` for every subspace
`D' ⊆ D` stable under `φ` and `N`, with the induced filtration on `D'_K` (Fontaine–Ouyang,
Definition 8.39; Fontaine, Exposé III, §4.4.3). In the sources `v` is the `p`-adic valuation,
normalized by `v(p) = 1`. Fontaine–Ouyang call these modules *admissible*; by their Remark 8.55,
*weakly admissible* is the older name, Fontaine's *faiblement admissible*. -/
structure IsWeaklyAdmissible [FiniteDimensional K₀ D] (v : AddValuation K₀ (WithTop ℤ)) :
    Prop where
  /-- `t_H(D) = t_N(D)`. -/
  hodgeNumber_eq_newtonNumber : M.hodgeNumber = M.newtonNumber v
  /-- `t_H(D') ≤ t_N(D')` for every subspace `D'` stable under `φ` and `N`. -/
  hodgeNumber_restrict_le (D' : Submodule K₀ D) (h : M.IsStable D') :
    (M.restrict D' h).hodgeNumber ≤ (M.restrict D' h).newtonNumber v

variable [FiniteDimensional K₀ D] {v : AddValuation K₀ (WithTop ℤ)}

/-- Fontaine–Ouyang, Remark 8.40, and Fontaine, Exposé III, §4.4.2: for an additive valuation
`v` with `v ∘ σ = v`, a finite-dimensional filtered `(φ, N)`-module `D` is weakly admissible if
and only if `t_H(D) = t_N(D)` and `t_H(D ⧸ D') ≥ t_N(D ⧸ D')` for every subspace `D'` stable
under `φ` and `N`, with the quotient filtration on `(D ⧸ D')_K`. -/
theorem isWeaklyAdmissible_iff_quotient (hv : ∀ x, v (σ x) = v x) :
    M.IsWeaklyAdmissible v ↔ M.hodgeNumber = M.newtonNumber v ∧
      ∀ (D' : Submodule K₀ D) (h : M.IsStable D'),
        (M.quotient D' h).newtonNumber v ≤ (M.quotient D' h).hodgeNumber := by
  refine ⟨fun hM => ⟨hM.hodgeNumber_eq_newtonNumber, fun D' h => ?_⟩,
    fun hM => ⟨hM.1, fun D' h => ?_⟩⟩
  · have h1 := hM.hodgeNumber_restrict_le D' h
    have h2 := hM.hodgeNumber_eq_newtonNumber
    have h3 := M.hodgeNumber_eq_restrict_add_quotient D' h
    have h4 := M.toPhiNModule.newtonNumber_eq_restrict_add_quotient v hv D' h
    rw [← restrict_toPhiNModule, ← quotient_toPhiNModule] at h4
    linarith
  · have h1 := hM.2 D' h
    have h2 := hM.1
    have h3 := M.hodgeNumber_eq_restrict_add_quotient D' h
    have h4 := M.toPhiNModule.newtonNumber_eq_restrict_add_quotient v hv D' h
    rw [← restrict_toPhiNModule, ← quotient_toPhiNModule] at h4
    linarith

/-- A one-dimensional filtered `(φ, N)`-module `D` is weakly admissible, for an additive valuation
`v` with `v ∘ σ = v`, if and only if `t_H(D) = t_N(D)`: its only stable subspaces are `0` and
`D`. -/
theorem isWeaklyAdmissible_iff_of_finrank_eq_one (hv : ∀ x, v (σ x) = v x)
    (hD : finrank K₀ D = 1) : M.IsWeaklyAdmissible v ↔ M.hodgeNumber = M.newtonNumber v := by
  refine ⟨fun hM => hM.hodgeNumber_eq_newtonNumber, fun hM => ⟨hM, fun D' h => ?_⟩⟩
  have hle := Submodule.finrank_le D'
  rcases Nat.lt_or_ge (finrank K₀ D') 1 with h0 | h1
  · have h0' : finrank K₀ D' = 0 := by omega
    rw [hodgeNumber_eq_zero_of_finrank_eq_zero _ h0',
      PhiNModule.newtonNumber_eq_zero_of_finrank_eq_zero v _ h0']
  · have hq : finrank K₀ (D ⧸ D') = 0 := by
      have := Submodule.finrank_quotient_add_finrank D'
      omega
    have hH := M.hodgeNumber_eq_restrict_add_quotient D' h
    have hN := M.toPhiNModule.newtonNumber_eq_restrict_add_quotient v hv D' h
    rw [← restrict_toPhiNModule, ← quotient_toPhiNModule] at hN
    rw [hodgeNumber_eq_zero_of_finrank_eq_zero _ hq] at hH
    rw [PhiNModule.newtonNumber_eq_zero_of_finrank_eq_zero v _ hq] at hN
    linarith

end FilteredPhiNModule
