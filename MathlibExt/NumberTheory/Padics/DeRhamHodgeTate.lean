/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.Padics.DeRhamFiltration
public import MathlibExt.NumberTheory.Padics.HodgeTate.Decomposition

/-!
# De Rham representations are Hodge–Tate

Let `K` be finite over `ℚ_p` inside `ℚ̄_p`, `G_K = Gal(ℚ̄_p/K)` and `ρ` a finite-dimensional
`ℚ_p`-linear representation of `Gal(ℚ̄_p/ℚ_p)` on `V`. With the filtration
`Fil^i D_dR(V) = (Fil^i B_dR ⊗_{ℚ_p} V)^{G_K}` (`Representation.deRhamFiltration`) and its graded
pieces `gr^i D_dR(V)` (`Representation.deRhamGraded`), following J.-M. Fontaine,
*Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §3.4 p. 140,
§3.7 pp. 141–142 and Théorème 3.8 (i) p. 142, we show:

* the filtration of `D_dR(V)` is finite: `Fil^i D_dR(V) = D_dR(V)` for `i` small enough
  (`Representation.exists_deRhamFiltration_eq_periods`) and `Fil^i D_dR(V) = 0` for `i` large
  enough (`Representation.exists_deRhamFiltration_eq_bot`);
* `dim_K D_dR(V) = Σᵢ dim_K gr^i D_dR(V)`
  (`Representation.finrank_periods_galoisBDeRham_eq_finsum`);
* `dim_K gr^i D_dR(V) ≤ h_{-i} = dim_K (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`
  (`Representation.finrank_deRhamGraded_le`), hence `dim_K D_dR(V) ≤ dim_K D_HT(V)`
  (`Representation.finrank_periods_galoisBDeRham_le`);
* **de Rham representations are Hodge–Tate** (`Representation.IsDeRham.isHodgeTate`), with
  `dim_K gr^i D_dR(V) = h_{-i}` (`Representation.IsDeRham.finrank_deRhamGraded`) and
  `gr^i D_dR(V) ≅ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`
  (`Representation.IsDeRham.deRhamGradedToTwistPeriods_bijective`);
* `ℚ_p(1)` is de Rham (`Representation.isDeRham_cyclotomic`): `t⁻¹ ⊗ 1 ∈ D_dR(ℚ_p(1))`
  (`Representation.zpow_neg_one_tmul_mem_periods_cyclotomic`), so the one-dimensional
  `D_dR(ℚ_p(1))` is `K t⁻¹`, and its filtration jumps at `-1`: `gr^i D_dR(ℚ_p(1))` has dimension
  `1` for `i = -1` and `0` otherwise (`Representation.finrank_deRhamGraded_cyclotomic`).

## Sign conventions

The Hodge–Tate numbers are those of `Representation.hodgeTateNumber`:
`hᵢ = dim_K (ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}`, so that `ℚ_p(1)` has `h₁ = 1`. The graded piece of the
de Rham filtration in degree `i` has dimension `h_{-i}`: for `ℚ_p(1)`, `t⁻¹ ∈ Fil^{-1} B_dR` and
`t⁻¹ ∉ Fil^0 B_dR`, so the jump is at `-1`.
-/

@[expose] public noncomputable section

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplexInt
open scoped TensorProduct

namespace Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝕥" => logTeichmuller p (untilt_epsilon p)

/-- If `f ≤ g` pointwise, both have finite support and `Σ f = Σ g`, then `f = g`. -/
private theorem eq_of_finsum_eq_of_le {f g : ℤ → ℕ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hle : ∀ i, f i ≤ g i)
    (heq : ∑ᶠ i, f i = ∑ᶠ i, g i) (i : ℤ) : f i = g i := by
  classical
  let s := hf.toFinset ∪ hg.toFinset
  have hfs : Function.support f ⊆ s := fun x hx =>
    Finset.mem_union_left _ (hf.mem_toFinset.2 hx)
  have hgs : Function.support g ⊆ s := fun x hx =>
    Finset.mem_union_right _ (hg.mem_toFinset.2 hx)
  rw [finsum_eq_sum_of_support_subset f hfs, finsum_eq_sum_of_support_subset g hgs] at heq
  by_cases hi : i ∈ s
  · exact (Finset.sum_eq_sum_iff_of_le fun j _ => hle j).1 heq i hi
  · rw [Function.notMem_support.1 fun h => hi (hfs h),
      Function.notMem_support.1 fun h => hi (hgs h)]

section FiniteDimensional

variable (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

/-- `B_dR^{G_K} ≅ K` is finite-dimensional over `ℚ_p`. -/
private theorem finite_fixedSubalgebra_galoisBDeRhamHom :
    Module.Finite ℚ_[p] (fixedSubalgebra 𝔹 ⇑(galoisBDeRhamHom p) K.fixingSubgroup) :=
  Module.Finite.equiv (deRhamFixedSubalgebraEquiv p K).toLinearEquiv

/-- **The filtration of `D_dR(V)` is exhaustive** (Fontaine, *Représentations p-adiques
semi-stables*, Exposé III, §3.4 p. 140 and §3.7 p. 141): `Fil^i D_dR(V) = D_dR(V)` for `i` small
enough. -/
theorem exists_deRhamFiltration_eq_periods [FiniteDimensional ℚ_[p] V] :
    ∃ a, ∀ i ≤ a,
      ρ.deRhamFiltration K i = ρ.periods (galoisBDeRham p) K.fixingSubgroup :=
  ρ.exists_periodsFiltration_eq_periods (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup)
    (fixedSubalgebra_mul_mem_filBDeRham p K) (restrictScalars_filBDeRham_antitone p)
    (exists_mem_filBDeRham p)

/-- **The filtration of `D_dR(V)` is separated** (Fontaine, *Représentations p-adiques
semi-stables*, Exposé III, §3.4 p. 140 and §3.7 p. 141): `Fil^i D_dR(V) = 0` for `i` large
enough. -/
theorem exists_deRhamFiltration_eq_bot [FiniteDimensional ℚ_[p] V] :
    ∃ b, ∀ i, b ≤ i → ρ.deRhamFiltration K i = ⊥ := by
  have := finite_fixedSubalgebra_galoisBDeRhamHom K
  exact ρ.exists_periodsFiltration_eq_bot (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup)
    (fixedSubalgebra_mul_mem_filBDeRham p K) (restrictScalars_filBDeRham_antitone p)
    (eq_zero_of_forall_mem_filBDeRham p)

/-- Only finitely many graded pieces `gr^i D_dR(V)` are nonzero. -/
theorem finite_support_finrank_deRhamGraded [FiniteDimensional ℚ_[p] V] :
    (Function.support fun i => Module.finrank
      (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup) (ρ.deRhamGraded K i)).Finite := by
  have := finite_fixedSubalgebra_galoisBDeRhamHom K
  exact ρ.finite_support_finrank_periodsGraded
    (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup)
    (fixedSubalgebra_mul_mem_filBDeRham p K) (restrictScalars_filBDeRham_antitone p)
    (exists_mem_filBDeRham p) (eq_zero_of_forall_mem_filBDeRham p)

/-- **`dim_K D_dR(V) = Σᵢ dim_K gr^i D_dR(V)`** (Fontaine, *Représentations p-adiques
semi-stables*, Exposé III, §3.4 p. 140 and §3.7 p. 142): for `K` finite over `ℚ_p` and a
finite-dimensional `V`, the dimension of `D_dR(V)` over `B_dR^{G_K} = K` is the sum of the
dimensions of the graded pieces of its filtration. -/
theorem finrank_periods_galoisBDeRham_eq_finsum [FiniteDimensional ℚ_[p] V] :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.periods (galoisBDeRham p) K.fixingSubgroup) =
      ∑ᶠ i, Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.deRhamGraded K i) := by
  have := finite_fixedSubalgebra_galoisBDeRhamHom K
  exact ρ.finrank_periods_eq_finsum_finrank_periodsGraded
    (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup)
    (fixedSubalgebra_mul_mem_filBDeRham p K) (restrictScalars_filBDeRham_antitone p)
    (exists_mem_filBDeRham p) (eq_zero_of_forall_mem_filBDeRham p)

/-- `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` is finite-dimensional over `ℚ_p`, of dimension `[K : ℚ_p] h_{-i}`. -/
private theorem finite_twistPeriods_and_finrank [FiniteDimensional ℚ_[p] V] (i : ℤ) :
    FiniteDimensional ℚ_[p] (ρ.twistPeriods K i) ∧
      Module.finrank ℚ_[p] (ρ.twistPeriods K i) =
        Module.finrank ℚ_[p] K * ρ.hodgeTateNumber K (-i) := by
  have hC := isRegularPeriodRing_of_isField (Field.toIsField ℂ_[p]) (PadicComplex.galoisAlgHom p)
    K.fixingSubgroup
  have : Module.Finite
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i) :=
    hC.finite_periods (ρ.tateTwist i)
  have : Module.Free
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i) :=
    hC.free_periods (ρ.tateTwist i)
  have : Module.Finite ℚ_[p]
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup) :=
    Module.Finite.equiv (PadicComplex.galoisFixedSubalgebraEquiv p K).toLinearEquiv
  refine ⟨Module.Finite.trans
    (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup) _, ?_⟩
  rw [hodgeTateNumber, neg_neg,
    (PadicComplex.galoisFixedSubalgebraEquiv p K).toLinearEquiv.finrank_eq,
    Module.finrank_mul_finrank]

/-- `dim_{ℚ_p} gr^i D_dR(V) = [K : ℚ_p] dim_K gr^i D_dR(V)`. -/
private theorem finrank_padic_deRhamGraded (i : ℤ) :
    Module.finrank ℚ_[p] (ρ.deRhamGraded K i) = Module.finrank ℚ_[p] K *
      Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.deRhamGraded K i) := by
  have := finite_fixedSubalgebra_galoisBDeRhamHom K
  rw [(deRhamFixedSubalgebraEquiv p K).toLinearEquiv.finrank_eq]
  exact (ρ.finrank_mul_finrank_periodsGraded
    (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup)
    (fixedSubalgebra_mul_mem_filBDeRham p K) i).symm

/-- **`dim_K gr^i D_dR(V) ≤ h_{-i}`** (Fontaine, *Représentations p-adiques semi-stables*,
Exposé III, §3.7 p. 142): `gr^i D_dR(V)` embeds in `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`, of dimension
`h_{-i}` over `K` (`Representation.deRhamGradedToTwistPeriods_injective`). -/
theorem finrank_deRhamGraded_le [FiniteDimensional ℚ_[p] V] (i : ℤ) :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
      (ρ.deRhamGraded K i) ≤ ρ.hodgeTateNumber K (-i) := by
  obtain ⟨hfin, hdim⟩ := ρ.finite_twistPeriods_and_finrank K i
  refine Nat.le_of_mul_le_mul_left ?_ (Module.finrank_pos (R := ℚ_[p]) (M := K))
  rw [← finrank_padic_deRhamGraded, ← hdim]
  exact LinearMap.finrank_le_finrank_of_injective (deRhamGradedToTwistPeriods_injective ρ K i)

/-- The Hodge–Tate numbers `h_{-i}` have finite support. -/
private theorem finite_support_hodgeTateNumber_neg [FiniteDimensional ℚ_[p] V] :
    (Function.support fun i => ρ.hodgeTateNumber K (-i)).Finite :=
  (finite_support_hodgeTateNumber K ρ).preimage neg_injective.injOn

omit [FiniteDimensional ℚ_[p] K] in
/-- `Σᵢ h_{-i} = Σᵢ hᵢ`. -/
private theorem finsum_hodgeTateNumber_neg :
    ∑ᶠ i, ρ.hodgeTateNumber K (-i) = ∑ᶠ i, ρ.hodgeTateNumber K i :=
  finsum_comp_equiv (Equiv.neg ℤ) (f := ρ.hodgeTateNumber K)

/-- **`dim_K D_dR(V) ≤ dim_K D_HT(V)`** (Fontaine, *Représentations p-adiques semi-stables*,
Exposé III, §3.7 p. 142): for `K` finite over `ℚ_p` and a finite-dimensional `V`,
`dim_K D_dR(V) = Σᵢ dim_K gr^i D_dR(V) ≤ Σᵢ h_{-i} = dim_K D_HT(V)`, the dimensions being taken
over `B_dR^{G_K} = K` and `B_HT^{G_K} = K`. -/
theorem finrank_periods_galoisBDeRham_le [FiniteDimensional ℚ_[p] V] :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.periods (galoisBDeRham p) K.fixingSubgroup) ≤
      Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p)
        K.fixingSubgroup) (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) := by
  rw [finrank_periods_galoisBDeRham_eq_finsum, finrank_periods_hodgeTateAction_eq_finsum,
    ← finsum_hodgeTateNumber_neg]
  exact finsum_le_finsum (ρ.finite_support_finrank_deRhamGraded K)
    (ρ.finite_support_hodgeTateNumber_neg K) (ρ.finrank_deRhamGraded_le K)

end FiniteDimensional

variable {ρ : Representation ℚ_[p] (Galois p) V} {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K]

/-- **De Rham representations are Hodge–Tate** (Fontaine, *Représentations p-adiques
semi-stables*, Astérisque 223, Exposé III, Théorème 3.8 (i) p. 142): for `K` finite over `ℚ_p`,
if `V` is de Rham over `K`, then `dim_{ℚ_p} V = dim_K D_dR(V) ≤ dim_K D_HT(V) ≤ dim_{ℚ_p} V`, so
`V` is Hodge–Tate over `K`. -/
theorem IsDeRham.isHodgeTate (h : ρ.IsDeRham K) : ρ.IsHodgeTate K := by
  obtain ⟨hV, hdim⟩ := h
  refine ⟨hV, le_antisymm (finrank_periods_hodgeTateAction_le K ρ) ?_⟩
  rw [← hdim]
  exact finrank_periods_galoisBDeRham_le ρ K

/-- **The Hodge–Tate numbers of a de Rham representation are the jumps of its filtration**
(Fontaine, *Représentations p-adiques semi-stables*, Exposé III, Théorème 3.8 (i) p. 142): for `K`
finite over `ℚ_p` and `V` de Rham over `K`, `dim_K gr^i D_dR(V) = h_{-i}`, the dimension of
`(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` over `K`. -/
theorem IsDeRham.finrank_deRhamGraded (h : ρ.IsDeRham K) (i : ℤ) :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
      (ρ.deRhamGraded K i) = ρ.hodgeTateNumber K (-i) := by
  have := h.1
  refine eq_of_finsum_eq_of_le (ρ.finite_support_finrank_deRhamGraded K)
    (ρ.finite_support_hodgeTateNumber_neg K) (ρ.finrank_deRhamGraded_le K) ?_ i
  rw [← finrank_periods_galoisBDeRham_eq_finsum, h.2, finsum_hodgeTateNumber_neg,
    (isHodgeTate_iff_finsum_hodgeTateNumber K ρ).1 h.isHodgeTate]

/-- **`gr^i D_dR(V) ≅ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` for a de Rham representation** (Fontaine,
*Représentations p-adiques semi-stables*, Exposé III, Théorème 3.8 (i) p. 142): the inclusion
`gr^i D_dR(V) → (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` is bijective, so that `gr D_dR(V) ≅ D_HT(V)`. -/
theorem IsDeRham.deRhamGradedToTwistPeriods_bijective (h : ρ.IsDeRham K) (i : ℤ) :
    Function.Bijective (deRhamGradedToTwistPeriods ρ K i) := by
  have := h.1
  obtain ⟨hfin, hdim⟩ := ρ.finite_twistPeriods_and_finrank K i
  have hinj := deRhamGradedToTwistPeriods_injective ρ K i
  have : FiniteDimensional ℚ_[p] (ρ.deRhamGraded K i) := FiniteDimensional.of_injective _ hinj
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_padic_deRhamGraded, hdim, h.finrank_deRhamGraded i]

/-! ### `ℚ_p(1)` -/

omit [FiniteDimensional ℚ_[p] K] in
variable (K) in
/-- **`t⁻¹ ⊗ 1 ∈ D_dR(ℚ_p(1))`**: for every subfield `K` of `ℚ̄_p`, `σ(t⁻¹) ⊗ χ(σ) = t⁻¹ ⊗ 1`
since `σ(t) = χ(σ) t`. -/
theorem zpow_neg_one_tmul_mem_periods_cyclotomic :
    (algebraMap 𝔹⁺ 𝔹 𝕥 ^ (-1 : ℤ)) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) ∈
      (cyclotomic p).periods (galoisBDeRham p) K.fixingSubgroup := by
  rw [mem_periods]
  intro σ _
  have hχ : cyclotomicScalar p σ ^ (-1 : ℤ) * cyclotomicScalar p σ = 1 := by
    rw [zpow_neg_one, inv_mul_cancel₀ (cyclotomicScalar_ne_zero p σ)]
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    galoisBDeRham_algebraMap_logTeichmuller_epsilon_zpow, cyclotomic_apply, mul_one,
    TensorProduct.smul_tmul, smul_eq_mul, hχ]

omit [FiniteDimensional ℚ_[p] K] in
variable (K) in
/-- **`ℚ_p(1)` is de Rham** over every `K` finite over `ℚ_p` inside `ℚ̄_p`: `D_dR(ℚ_p(1))`
contains the nonzero vector `t⁻¹ ⊗ 1`, so it has dimension `1 = dim_{ℚ_p} ℚ_p(1)`. -/
theorem isDeRham_cyclotomic : (cyclotomic p).IsDeRham K := by
  have hS := isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup
  have hne : (algebraMap 𝔹⁺ 𝔹 𝕥 ^ (-1 : ℤ)) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) ≠ 0 := by
    intro h0
    have h1 := congrArg (_root_.TensorProduct.rid ℚ_[p] 𝔹) h0
    rw [_root_.TensorProduct.rid_tmul, one_smul, map_zero] at h1
    exact zpow_ne_zero _ (algebraMap_logTeichmuller_epsilon_ne_zero p) h1
  refine ⟨inferInstance, le_antisymm (hS.finrank_periods_le (cyclotomic p)) ?_⟩
  rw [Module.finrank_self]
  exact (cyclotomic p).one_le_finrank_periods hS (zpow_neg_one_tmul_mem_periods_cyclotomic K) hne

variable (K) in
/-- **The filtration of `D_dR(ℚ_p(1))` jumps at `-1`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`,
`gr^i D_dR(ℚ_p(1))` has dimension `1` over `K` for `i = -1` and `0` otherwise, matching
`h₁ = 1` (`Representation.hodgeTateNumber_cyclotomic`), as `D_dR(ℚ_p(1)) = K t⁻¹` with
`t⁻¹ ∈ Fil^{-1} B_dR` and `t⁻¹ ∉ Fil^0 B_dR`. -/
theorem finrank_deRhamGraded_cyclotomic (i : ℤ) :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
      ((cyclotomic p).deRhamGraded K i) = if i = -1 then 1 else 0 := by
  rw [(isDeRham_cyclotomic K).finrank_deRhamGraded, hodgeTateNumber_cyclotomic]
  simp only [neg_eq_iff_eq_neg]

end Representation
