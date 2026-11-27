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
* `FilteredPhiNModule.Hom`: morphisms of filtered `(φ, N)`-modules.

## Main results

* `FilteredPhiNModule.hodgeNumber_eq_restrict_add_quotient`: additivity of `t_H`.
* `FilteredPhiNModule.isWeaklyAdmissible_iff_quotient`: the equivalent condition on quotients.
* `FilteredPhiNModule.isWeaklyAdmissible_iff_of_finrank_eq_one`: a one-dimensional module is
  weakly admissible if and only if `t_H(D) = t_N(D)`.
* `FilteredPhiNModule.IsWeaklyAdmissible.restrict_of_hodgeNumber_eq`,
  `FilteredPhiNModule.IsWeaklyAdmissible.quotient_of_hodgeNumber_eq`: a stable subspace `D'` of a
  weakly admissible module with `t_H(D') = t_N(D')`, and the quotient by it, are weakly
  admissible.
* Fontaine–Ouyang, Proposition 8.41, the content of "the weakly admissible modules form an
  abelian category": for a morphism `η` of weakly admissible modules, the kernel
  (`FilteredPhiNModule.IsWeaklyAdmissible.ker`), the image
  (`FilteredPhiNModule.IsWeaklyAdmissible.range`) and the cokernel
  (`FilteredPhiNModule.IsWeaklyAdmissible.coker`) are weakly admissible, and `η` is strict for
  the filtrations (`FilteredPhiNModule.IsWeaklyAdmissible.map_fil_eq_range_inf_fil`).

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.3–§8.2.5: Definitions 8.34, 8.36 and 8.39, (8.11), Remark 8.40, Proposition 8.41;
  Remark 8.55.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.3.2–§4.3.3 pp. 148–149 and §4.4.1–§4.4.4 pp. 150–151.
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

namespace FilteredPhiNModule

variable {σ p K} {D : Type*} [AddCommGroup D] [Module K₀ D]

/-! ### Stable subspaces of a stable subspace and of a quotient -/

section QuotientHelpers

variable {D' : Submodule K₀ D}

/-- The preimage in `D` of a subspace of `D ⧸ D'` contains `D'`. -/
private theorem le_comap_mkQ (C : Submodule K₀ (D ⧸ D')) : D' ≤ C.comap D'.mkQ := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero D').mpr hx]
  exact C.zero_mem

/-- The quotient map from the preimage in `D` of a subspace `C` of `D ⧸ D'` onto `C`. -/
private noncomputable def toSub (C : Submodule K₀ (D ⧸ D')) : C.comap D'.mkQ →ₗ[K₀] C :=
  D'.mkQ.restrict fun _ hx => hx

private theorem toSub_surjective (C : Submodule K₀ (D ⧸ D')) :
    Function.Surjective (toSub C) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := D'.mkQ_surjective y
  exact ⟨⟨x, hy⟩, rfl⟩

private theorem exact_inclusion_toSub (C : Submodule K₀ (D ⧸ D')) :
    Function.Exact (Submodule.inclusion (le_comap_mkQ C)) (toSub C) := by
  intro y
  constructor
  · intro hy
    have hy' : (y : D) ∈ D' := by
      have := congrArg Subtype.val hy
      simpa [toSub, Submodule.Quotient.mk_eq_zero] using this
    exact ⟨⟨y, hy'⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero D').mpr x.2)

end QuotientHelpers

section Subobjects

variable {M : FilteredPhiNModule σ p K D} [FiniteDimensional K₀ D]

/-- For a stable subspace `D'` of a finite-dimensional filtered `(φ, N)`-module `D` and a stable
subspace `D''` of the restriction of `D` to `D'`, the restriction of that restriction to `D''`
has the Hodge number of the restriction of `D` to the image of `D''` in `D`. -/
theorem hodgeNumber_restrict_restrict {D' : Submodule K₀ D} (h : M.IsStable D')
    {D'' : Submodule K₀ D'} (h' : (M.restrict D' h).IsStable D'') :
    ((M.restrict D' h).restrict D'' h').hodgeNumber =
      (M.restrict (D''.map D'.subtype) (h.map_subtype h')).hodgeNumber := by
  set e := Submodule.equivMapOfInjective D'.subtype D'.injective_subtype D''
  have hcomp : D'.subtype ∘ₗ D''.subtype =
      (D''.map D'.subtype).subtype ∘ₗ (e : D'' →ₗ[K₀] _) := by
    ext
    rfl
  have hfil : ((M.restrict D' h).restrict D'' h').fil =
      (M.restrict (D''.map D'.subtype) (h.map_subtype h')).fil.comap
        (e.baseChange K₀ K _ _ : K ⊗[K₀] D'' →ₗ[K] _) (LinearEquiv.injective _) := by
    ext i : 1
    simp only [restrict_fil_fil, DecreasingFiltration.comap_fil, ← Submodule.comap_comp,
      LinearEquiv.coe_baseChange, ← LinearMap.baseChange_comp, hcomp]
  rw [hodgeNumber, hfil, DecreasingFiltration.hodgeNumber_comap_linearEquiv]
  rfl

/-- For an additive valuation `v` with `v ∘ σ = v`, a stable subspace `D'` of a
finite-dimensional filtered `(φ, N)`-module `D` and a stable subspace `D''` of the restriction of
`D` to `D'`, the restriction of that restriction to `D''` has the Newton number of the restriction
of `D` to the image of `D''` in `D`. -/
theorem newtonNumber_restrict_restrict {v : AddValuation K₀ (WithTop ℤ)}
    (hv : ∀ x, v (σ x) = v x) {D' : Submodule K₀ D} (h : M.IsStable D')
    {D'' : Submodule K₀ D'} (h' : (M.restrict D' h).IsStable D'') :
    ((M.restrict D' h).restrict D'' h').newtonNumber v =
      (M.restrict (D''.map D'.subtype) (h.map_subtype h')).newtonNumber v :=
  PhiNModule.newtonNumber_eq_of_linearEquiv v hv _ _
    (Submodule.equivMapOfInjective D'.subtype D'.injective_subtype D'') fun _ => rfl

variable {D' : Submodule K₀ D} (h : M.IsStable D') {C : Submodule K₀ (D ⧸ D')}
  (hC : (M.quotient D' h).IsStable C)

include hC in
/-- Additivity of `t_N` along `0 → D' → C.comap D'.mkQ → C → 0`. -/
private theorem newtonNumber_comap_mkQ {v : AddValuation K₀ (WithTop ℤ)}
    (hv : ∀ x, v (σ x) = v x) :
    (M.restrict (C.comap D'.mkQ) (h.comap_mkQ hC)).newtonNumber v =
      (M.restrict D' h).newtonNumber v + ((M.quotient D' h).restrict C hC).newtonNumber v :=
  PhiNModule.newtonNumber_eq_add_of_exact v hv (Submodule.inclusion_injective _)
    (toSub_surjective C) (exact_inclusion_toSub C) (fun _ => rfl) fun _ => rfl

include hC in
/-- Additivity of `t_H` along `0 → D' → C.comap D'.mkQ → C → 0`: the filtration of `C` induced
from the quotient filtration of `D ⧸ D'` is the quotient of the filtration of `C.comap D'.mkQ`
induced from `D`. -/
private theorem hodgeNumber_comap_mkQ :
    (M.restrict (C.comap D'.mkQ) (h.comap_mkQ hC)).hodgeNumber =
      (M.restrict D' h).hodgeNumber + ((M.quotient D' h).restrict C hC).hodgeNumber := by
  set D₂ := C.comap D'.mkQ
  have key := (M.restrict D₂ (h.comap_mkQ hC)).fil.hodgeNumber_eq_add_of_exact
    (baseChange_injective (K := K) (Submodule.inclusion_injective (le_comap_mkQ C)))
    (baseChange_surjective (K := K) (toSub_surjective C))
    (baseChange_exact (exact_inclusion_toSub C) (toSub_surjective C))
  have h1 : (M.restrict D₂ (h.comap_mkQ hC)).fil.comap
      ((Submodule.inclusion (le_comap_mkQ C)).baseChange K)
      (baseChange_injective (Submodule.inclusion_injective (le_comap_mkQ C))) =
      (M.restrict D' h).fil := by
    ext i : 1
    simp only [restrict_fil_fil, DecreasingFiltration.comap_fil, ← Submodule.comap_comp,
      ← LinearMap.baseChange_comp, Submodule.subtype_comp_inclusion]
  have hcomm : D'.mkQ.baseChange K ∘ₗ D₂.subtype.baseChange K =
      C.subtype.baseChange K ∘ₗ (toSub C).baseChange K := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker (D'.mkQ.baseChange K) ≤
      LinearMap.range (D₂.subtype.baseChange K) := by
    rw [(baseChange_exact (LinearMap.exact_subtype_mkQ D') D'.mkQ_surjective).linearMap_ker_eq,
      ← Submodule.subtype_comp_inclusion D' D₂ (le_comap_mkQ C), LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have h2 := DecreasingFiltration.comap_map_eq_map_comap M.fil
    (baseChange_injective (K := K) D₂.injective_subtype)
    (baseChange_surjective (K := K) D'.mkQ_surjective)
    (baseChange_injective (K := K) C.injective_subtype)
    (baseChange_surjective (K := K) (toSub_surjective C)) hcomm hker
  simp only [hodgeNumber]
  rw [key, h1]
  exact congrArg (_ + ·) (congrArg DecreasingFiltration.hodgeNumber h2.symm)

end Subobjects

namespace IsWeaklyAdmissible

variable {M : FilteredPhiNModule σ p K D} [FiniteDimensional K₀ D] {v : AddValuation K₀ (WithTop ℤ)}

/-- A stable subspace `D'` of a weakly admissible filtered `(φ, N)`-module `D`, for an additive
valuation `v` with `v ∘ σ = v`, is weakly admissible with the induced filtration as soon as
`t_H(D') = t_N(D')` (Fontaine, Exposé III, §4.4.4 (ii)). -/
theorem restrict_of_hodgeNumber_eq (hM : M.IsWeaklyAdmissible v) (hv : ∀ x, v (σ x) = v x)
    {D' : Submodule K₀ D} (h : M.IsStable D')
    (heq : (M.restrict D' h).hodgeNumber = (M.restrict D' h).newtonNumber v) :
    (M.restrict D' h).IsWeaklyAdmissible v where
  hodgeNumber_eq_newtonNumber := heq
  hodgeNumber_restrict_le D'' h' := by
    rw [hodgeNumber_restrict_restrict, newtonNumber_restrict_restrict hv]
    exact hM.hodgeNumber_restrict_le _ _

/-- The quotient of a weakly admissible filtered `(φ, N)`-module `D`, for an additive valuation
`v` with `v ∘ σ = v`, by a stable subspace `D'` is weakly admissible with the quotient filtration
as soon as `t_H(D') = t_N(D')` (Fontaine, Exposé III, §4.4.4 (ii)). -/
theorem quotient_of_hodgeNumber_eq (hM : M.IsWeaklyAdmissible v) (hv : ∀ x, v (σ x) = v x)
    {D' : Submodule K₀ D} (h : M.IsStable D')
    (heq : (M.restrict D' h).hodgeNumber = (M.restrict D' h).newtonNumber v) :
    (M.quotient D' h).IsWeaklyAdmissible v where
  hodgeNumber_eq_newtonNumber := by
    have h1 := M.hodgeNumber_eq_restrict_add_quotient D' h
    have h2 := M.toPhiNModule.newtonNumber_eq_restrict_add_quotient v hv D' h
    rw [← restrict_toPhiNModule, ← quotient_toPhiNModule] at h2
    have h3 := hM.hodgeNumber_eq_newtonNumber
    linarith
  hodgeNumber_restrict_le C hC := by
    have h1 := hodgeNumber_comap_mkQ h hC
    have h2 := newtonNumber_comap_mkQ h hC hv
    have h3 := hM.hodgeNumber_restrict_le _ (h.comap_mkQ hC)
    linarith

end IsWeaklyAdmissible

/-! ### Morphisms and the abelian category -/

section Hom

variable {D₁ D₂ : Type*} [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂]

/-- A morphism of filtered `(φ, N)`-modules `M₁ → M₂` (Fontaine–Ouyang, Definition 8.34 (2);
Fontaine, Exposé III, §4.3.3): a morphism of `(φ, N)`-modules `η : D₁ → D₂` (a `K₀`-linear map
commuting with `φ` and `N`) whose extension of scalars `η_K : D₁_K → D₂_K` maps `Fil^i D₁_K`
into `Fil^i D₂_K` for every `i`. -/
structure Hom (M₁ : FilteredPhiNModule σ p K D₁) (M₂ : FilteredPhiNModule σ p K D₂) extends
    PhiNModule.Hom M₁.toPhiNModule M₂.toPhiNModule where
  /-- `η_K (Fil^i D₁_K) ⊆ Fil^i D₂_K` for every `i`. -/
  map_fil_le (i : ℤ) : (M₁.fil.Fil i).map (toLinearMap.baseChange K) ≤ M₂.fil.Fil i

variable {M₁ : FilteredPhiNModule σ p K D₁} {M₂ : FilteredPhiNModule σ p K D₂}

/-- `η_K` factors as the surjection onto `(Im η)_K` followed by the inclusion into `D₂_K`. -/
private theorem baseChange_eq_comp (η : M₁.Hom M₂) :
    η.toLinearMap.baseChange K = (LinearMap.range η.toLinearMap).subtype.baseChange K ∘ₗ
      η.toLinearMap.rangeRestrict.baseChange K := by
  rw [← LinearMap.baseChange_comp, LinearMap.subtype_comp_codRestrict]

private theorem exact_ker_rangeRestrict (η : M₁.Hom M₂) :
    Function.Exact (LinearMap.ker η.toLinearMap).subtype η.toLinearMap.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]

variable [FiniteDimensional K₀ D₁] [FiniteDimensional K₀ D₂] {v : AddValuation K₀ (WithTop ℤ)}

/-- The quotient filtration on `(Im η)_K` along `η_K : D₁_K → (Im η)_K`. -/
private noncomputable def coimFil (η : M₁.Hom M₂) :
    DecreasingFiltration K (K ⊗[K₀] LinearMap.range η.toLinearMap) :=
  M₁.fil.map (η.toLinearMap.rangeRestrict.baseChange K)
    (baseChange_surjective η.toLinearMap.surjective_rangeRestrict)

/-- The quotient filtration on `(Im η)_K` is finer than the filtration induced from `D₂_K`. -/
private theorem coimFil_le (η : M₁.Hom M₂) (i : ℤ) :
    (coimFil η).Fil i ≤ (M₂.restrict _ η.isStable_range).fil.Fil i := by
  rw [coimFil, DecreasingFiltration.map_fil, restrict_fil_fil, Submodule.map_le_iff_le_comap,
    ← Submodule.comap_comp, ← baseChange_eq_comp, ← Submodule.map_le_iff_le_comap]
  exact η.map_fil_le i

/-- The inequality chain in the proof of Fontaine–Ouyang, Proposition 8.41: for weakly admissible
`M₁` and `M₂` and a morphism `η`, the kernel and the image (with the filtration induced from
`D₂_K`) satisfy `t_H = t_N`, and the two filtrations of `(Im η)_K` have the same `t_H`. -/
private theorem chain (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) :
    (M₁.restrict _ η.isStable_ker).hodgeNumber =
        (M₁.restrict _ η.isStable_ker).newtonNumber v ∧
      (coimFil η).hodgeNumber = (M₂.restrict _ η.isStable_range).hodgeNumber ∧
      (M₂.restrict _ η.isStable_range).hodgeNumber =
        (M₂.restrict _ η.isStable_range).newtonNumber v := by
  have hN : M₁.newtonNumber v = (M₁.restrict _ η.isStable_ker).newtonNumber v +
      (M₂.restrict _ η.isStable_range).newtonNumber v :=
    PhiNModule.newtonNumber_eq_add_of_exact v hv
      (M' := (M₁.restrict _ η.isStable_ker).toPhiNModule)
      (M'' := (M₂.restrict _ η.isStable_range).toPhiNModule) (Submodule.injective_subtype _)
      η.toLinearMap.surjective_rangeRestrict (exact_ker_rangeRestrict η) (fun _ => rfl)
      fun x => Subtype.ext (η.map_φ x)
  have hH : M₁.hodgeNumber =
      (M₁.restrict _ η.isStable_ker).hodgeNumber + (coimFil η).hodgeNumber :=
    M₁.fil.hodgeNumber_eq_add_of_exact (baseChange_injective (Submodule.injective_subtype _))
      (baseChange_surjective η.toLinearMap.surjective_rangeRestrict)
      (baseChange_exact (exact_ker_rangeRestrict η) η.toLinearMap.surjective_rangeRestrict)
  have hle : (coimFil η).hodgeNumber ≤ (M₂.restrict _ η.isStable_range).hodgeNumber :=
    DecreasingFiltration.hodgeNumber_le_of_le (coimFil_le η)
  have hK := h₁.hodgeNumber_restrict_le _ η.isStable_ker
  have hI := h₂.hodgeNumber_restrict_le _ η.isStable_range
  have h₁eq := h₁.hodgeNumber_eq_newtonNumber
  refine ⟨by linarith, by linarith, by linarith⟩

namespace IsWeaklyAdmissible

/-- Fontaine–Ouyang, Proposition 8.41 (1): for an additive valuation `v` with `v ∘ σ = v`, the
kernel of a morphism `η` of weakly admissible filtered `(φ, N)`-modules, with the induced
filtration `Fil^i (Ker η)_K = (Ker η)_K ∩ Fil^i D₁_K`, is weakly admissible. -/
theorem ker (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) :
    (M₁.restrict (LinearMap.ker η.toLinearMap) η.isStable_ker).IsWeaklyAdmissible v :=
  h₁.restrict_of_hodgeNumber_eq hv η.isStable_ker (chain hv h₁ h₂ η).1

/-- For an additive valuation `v` with `v ∘ σ = v`, the image of a morphism `η` of weakly
admissible filtered `(φ, N)`-modules, with the filtration induced from the target, is weakly
admissible. -/
theorem range (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) :
    (M₂.restrict (LinearMap.range η.toLinearMap) η.isStable_range).IsWeaklyAdmissible v :=
  h₂.restrict_of_hodgeNumber_eq hv η.isStable_range (chain hv h₁ h₂ η).2.2

/-- Fontaine–Ouyang, Proposition 8.41 (2): for an additive valuation `v` with `v ∘ σ = v`, the
cokernel `D₂ ⧸ Im η` of a morphism `η` of weakly admissible filtered `(φ, N)`-modules, with the
quotient filtration (the image of `Fil^i D₂_K`), is weakly admissible. -/
theorem coker (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) :
    (M₂.quotient (LinearMap.range η.toLinearMap) η.isStable_range).IsWeaklyAdmissible v :=
  h₂.quotient_of_hodgeNumber_eq hv η.isStable_range (chain hv h₁ h₂ η).2.2

/-- Fontaine–Ouyang, Proposition 8.41 (3): for an additive valuation `v` with `v ∘ σ = v`, a
morphism `η` of weakly admissible filtered `(φ, N)`-modules is strict for the filtrations:
`η_K (Fil^i D₁_K) = η_K (D₁_K) ∩ Fil^i D₂_K` for every `i`. Equivalently, the natural bijection
from the coimage of `η` (with the quotient filtration) to its image (with the induced filtration)
is an isomorphism of filtered modules (Fontaine, Exposé III, §4.3.3). -/
theorem map_fil_eq_range_inf_fil (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) (η : M₁.Hom M₂) (i : ℤ) :
    (M₁.fil.Fil i).map (η.toLinearMap.baseChange K) =
      LinearMap.range (η.toLinearMap.baseChange K) ⊓ M₂.fil.Fil i := by
  have heq : coimFil η = (M₂.restrict _ η.isStable_range).fil :=
    DecreasingFiltration.eq_of_le_of_hodgeNumber_le (coimFil_le η) (chain hv h₁ h₂ η).2.1.ge
  have hi := congrArg (fun F => F.Fil i) heq
  simp only [coimFil, DecreasingFiltration.map_fil, restrict_fil_fil] at hi
  rw [baseChange_eq_comp, Submodule.map_comp, hi, Submodule.map_comap_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (baseChange_surjective η.toLinearMap.surjective_rangeRestrict))]

end IsWeaklyAdmissible

end Hom

end FilteredPhiNModule
