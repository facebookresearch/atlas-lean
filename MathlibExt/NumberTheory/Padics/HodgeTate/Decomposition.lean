/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.Padics.HodgeTate.Representation

/-!
# The graded decomposition of `D_HT(V)`

For a representation `ρ` of `Gal(ℚ̄_p / ℚ_p)` on a `ℚ_p`-vector space `V` and a subfield `K` of
`ℚ̄_p`, the module `D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}` splits along the grading
`B_HT ⊗_{ℚ_p} V = ⨁ᵢ ℂ_p tⁱ ⊗_{ℚ_p} V`: an element lies in `D_HT(V)` if and only if each of its
components lies in `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` (`Representation.mem_periods_hodgeTateAction_iff`),
so that `D_HT(V) ≅ ⨁ᵢ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` (`Representation.periodsHodgeTateEquiv`), compatibly
with the actions of `K ⊆ ℂ_p` (`Representation.hodgeTateComponent_C_smul`): `D_HT(V)` is a graded
`K`-vector space (Fontaine–Ouyang, §6.1, after Proposition 6.5; J.-M. Fontaine, *Représentations
p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §3.7 p. 141).
For `K` finite over `ℚ_p` and `V` finite-dimensional, this gives `dim_K D_HT(V) = Σᵢ hᵢ`
(`Representation.finrank_periods_hodgeTateAction_eq_finsum`), hence `Σᵢ hᵢ ≤ dim_{ℚ_p} V`, with
equality if and only if `V` is Hodge–Tate (`Representation.isHodgeTate_iff_finsum_hodgeTateNumber`).
-/

@[expose] public noncomputable section

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison
open scoped TensorProduct DirectSum

namespace Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

variable (p V) in
/-- **The component of degree `i`** of `B_HT ⊗_{ℚ_p} V = ⨁ₙ ℂ_p tⁿ ⊗_{ℚ_p} V`: the `ℚ_p`-linear map
`B_HT ⊗_{ℚ_p} V → ℂ_p ⊗_{ℚ_p} V` sending `f ⊗ v` to `fᵢ ⊗ v`, where `fᵢ` is the coefficient of
`tⁱ` in `f`. -/
def hodgeTateComponent (i : ℤ) : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V →ₗ[ℚ_[p]] ℂ_[p] ⊗[ℚ_[p]] V :=
  LinearMap.rTensor V
    ((Finsupp.lapply i).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ_[p]).toLinearMap)

/-- The component of degree `i` of `f ⊗ v` is `fᵢ ⊗ v`. -/
@[simp]
theorem hodgeTateComponent_tmul (i : ℤ) (f : ℂ_[p][T;T⁻¹]) (v : V) :
    hodgeTateComponent p V i (f ⊗ₜ v) = f.coeff i ⊗ₜ v :=
  rfl

/-- **The components of `σ x`**: the component of degree `i` of `(σ ⊗ ρ(σ)) x` is
`χ(σ)ⁱ (σ ⊗ ρ(σ))` applied to the component of degree `i` of `x`. -/
theorem hodgeTateComponent_map (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) (σ : Galois p)
    (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    hodgeTateComponent p V i
        (TensorProduct.map (PadicComplex.hodgeTateAction p σ).toLinearMap (ρ σ) x) =
      cyclotomicScalar p σ ^ i •
        TensorProduct.map (completionGalois p σ).toLinearMap (ρ σ)
          (hodgeTateComponent p V i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f v =>
    rw [TensorProduct.map_tmul, hodgeTateComponent_tmul, hodgeTateComponent_tmul,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
      PadicComplex.coeff_hodgeTateAction, TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

variable (p V) in
/-- The `ℚ_p`-linear isomorphism `B_HT ⊗_{ℚ_p} V ≃ (ℤ →₀ ℂ_p ⊗_{ℚ_p} V)` sending `x` to the family
of its components. -/
private def componentsEquiv : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V ≃ₗ[ℚ_[p]] ℤ →₀ ℂ_[p] ⊗[ℚ_[p]] V :=
  (LinearEquiv.rTensor V (AddMonoidAlgebra.coeffLinearEquiv ℚ_[p])).trans
    (TensorProduct.finsuppLeft ℚ_[p] ℚ_[p] ℂ_[p] V ℤ)

/-- The value at `i` of `componentsEquiv p V x` is the component of degree `i` of `x`. -/
private theorem componentsEquiv_apply (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) (i : ℤ) :
    componentsEquiv p V x i = hodgeTateComponent p V i x := by
  rw [componentsEquiv, LinearEquiv.trans_apply, TensorProduct.finsuppLeft_apply,
    hodgeTateComponent, LinearMap.rTensor_comp_apply]
  rfl

/-- An element of `B_HT ⊗_{ℚ_p} V` is zero if and only if all its components are zero. -/
theorem eq_zero_iff_forall_hodgeTateComponent_eq_zero (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    x = 0 ↔ ∀ i, hodgeTateComponent p V i x = 0 := by
  rw [← (componentsEquiv p V).map_eq_zero_iff, Finsupp.ext_iff]
  simp only [componentsEquiv_apply, Finsupp.coe_zero, Pi.zero_apply]

/-- Only finitely many components of an element of `B_HT ⊗_{ℚ_p} V` are nonzero. -/
theorem finite_support_hodgeTateComponent (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    (Function.support fun i => hodgeTateComponent p V i x).Finite := by
  have h : (fun i => hodgeTateComponent p V i x) = componentsEquiv p V x :=
    funext fun i => (componentsEquiv_apply x i).symm
  rw [h]
  exact (componentsEquiv p V x).support.finite_toSet.subset fun i hi =>
    Finsupp.mem_support_iff.2 hi

/-- The component of degree `j` of `y tⁱ`, the image of `y ∈ ℂ_p ⊗_{ℚ_p} V` under
`c ⊗ v ↦ c tⁱ ⊗ v`, is `y` if `j = i` and `0` otherwise. -/
theorem hodgeTateComponent_rTensor_lsingle (i j : ℤ) (y : ℂ_[p] ⊗[ℚ_[p]] V) :
    hodgeTateComponent p V j (LinearMap.rTensor V (AddMonoidAlgebra.lsingle (R := ℚ_[p]) i) y) =
      if j = i then y else 0 := by
  have h : ((Finsupp.lapply j).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ_[p]).toLinearMap).comp
      (AddMonoidAlgebra.lsingle (R := ℚ_[p]) (S := ℂ_[p]) i) =
        (Finsupp.lapply j).comp (Finsupp.lsingle i) := by
    ext c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.lsingle_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.lsingle_apply]
  rw [hodgeTateComponent, ← LinearMap.rTensor_comp_apply, h]
  split_ifs with hji
  · rw [hji, Finsupp.lapply_comp_lsingle_same, LinearMap.rTensor_id_apply]
  · rw [Finsupp.lapply_comp_lsingle_of_ne _ _ hji, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- **The graded decomposition of `D_HT(V)`, elementwise** (Fontaine–Ouyang, after
Proposition 6.5): `x ∈ B_HT ⊗_{ℚ_p} V` lies in `D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}` if and only if,
for every `i`, its component of degree `i` lies in `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`. -/
theorem mem_periods_hodgeTateAction_iff (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    x ∈ ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup ↔
      ∀ i, hodgeTateComponent p V i x ∈ ρ.twistPeriods K i := by
  simp only [mem_periods, mem_twistPeriods]
  constructor
  · intro h i σ hσ
    rw [← hodgeTateComponent_map, h σ hσ]
  · intro h σ hσ
    rw [← sub_eq_zero, eq_zero_iff_forall_hodgeTateComponent_eq_zero]
    intro i
    rw [map_sub, hodgeTateComponent_map, h i σ hσ, sub_self]

/-- If `y ∈ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`, then its image `y tⁱ` under `c ⊗ v ↦ c tⁱ ⊗ v` lies in
`D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}`. -/
theorem rTensor_lsingle_mem_periods_hodgeTateAction {ρ : Representation ℚ_[p] (Galois p) V}
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {i : ℤ} {y : ℂ_[p] ⊗[ℚ_[p]] V}
    (hy : y ∈ ρ.twistPeriods K i) :
    LinearMap.rTensor V (AddMonoidAlgebra.lsingle (R := ℚ_[p]) i) y ∈
      ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup := by
  refine (mem_periods_hodgeTateAction_iff ρ K _).2 fun j => ?_
  rw [hodgeTateComponent_rTensor_lsingle]
  split_ifs with hji
  · exact hji ▸ hy
  · exact zero_mem _

/-- For a family `φ` of `ℚ_p`-linear maps `(ℂ_p(i) ⊗ V)^{G_K} → D_HT(V)` such that `φ i y` has
component `y` in degree `i` and `0` in the other degrees, the component of degree `j` of the
image of `y` under the induced map on the direct sum is `y j`. -/
private theorem hodgeTateComponent_toModule {ρ : Representation ℚ_[p] (Galois p) V}
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {φ : ∀ i, ρ.twistPeriods K i →ₗ[ℚ_[p]]
      ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup}
    (hφ : ∀ i j (y : ρ.twistPeriods K i),
      hodgeTateComponent p V j (φ i y) = if j = i then (y : ℂ_[p] ⊗[ℚ_[p]] V) else 0)
    (y : ⨁ i, ρ.twistPeriods K i) (j : ℤ) :
    hodgeTateComponent p V j (DirectSum.toModule ℚ_[p] ℤ _ φ y) = y j := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, ZeroMemClass.coe_zero, map_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]
  | of i z =>
    rw [← DirectSum.lof_eq_of ℚ_[p], DirectSum.toModule_lof, hφ, DirectSum.lof_eq_of]
    split_ifs with h
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, ZeroMemClass.coe_zero]
  | add y z hy hz =>
    simp only [map_add, Submodule.coe_add, hy, hz, DirectSum.add_apply]

/-- For a family `φ` as in `hodgeTateComponent_toModule`, the induced map
`⨁ᵢ (ℂ_p(i) ⊗ V)^{G_K} → D_HT(V)` is bijective. -/
private theorem bijective_toModule {ρ : Representation ℚ_[p] (Galois p) V}
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {φ : ∀ i, ρ.twistPeriods K i →ₗ[ℚ_[p]]
      ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup}
    (hφ : ∀ i j (y : ρ.twistPeriods K i),
      hodgeTateComponent p V j (φ i y) = if j = i then (y : ℂ_[p] ⊗[ℚ_[p]] V) else 0) :
    Function.Bijective (DirectSum.toModule ℚ_[p] ℤ _ φ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => DirectSum.ext_iff.2 fun j => ?_,
    fun x => ?_⟩
  · refine Subtype.ext ?_
    rw [← hodgeTateComponent_toModule hφ y j, hy, DirectSum.zero_apply, ZeroMemClass.coe_zero,
      ZeroMemClass.coe_zero, map_zero]
  · have hfin := finite_support_hodgeTateComponent (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V)
    refine ⟨DFinsupp.mk hfin.toFinset fun i =>
      ⟨hodgeTateComponent p V i x, (mem_periods_hodgeTateAction_iff ρ K x).1 x.2 i⟩,
      Subtype.ext ?_⟩
    rw [← sub_eq_zero, eq_zero_iff_forall_hodgeTateComponent_eq_zero]
    intro j
    rw [map_sub, hodgeTateComponent_toModule hφ, sub_eq_zero, DFinsupp.mk_apply]
    split_ifs with hj
    · rfl
    · rw [ZeroMemClass.coe_zero]
      exact (Function.notMem_support.1 fun h => hj (hfin.mem_toFinset.2 h)).symm

/-- **The inclusion of degree `i`**, `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K} → D_HT(V)`, `y ↦ y tⁱ`: the
restriction of the `ℚ_p`-linear map `ℂ_p ⊗_{ℚ_p} V → B_HT ⊗_{ℚ_p} V`, `c ⊗ v ↦ c tⁱ ⊗ v`. -/
def hodgeTateInclusion (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (i : ℤ) :
    ρ.twistPeriods K i →ₗ[ℚ_[p]] ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup where
  toFun y := ⟨LinearMap.rTensor V (AddMonoidAlgebra.lsingle (R := ℚ_[p]) i) y,
    rTensor_lsingle_mem_periods_hodgeTateAction y.2⟩
  map_add' y z := Subtype.ext (map_add _ (y : ℂ_[p] ⊗[ℚ_[p]] V) z)
  map_smul' c y := Subtype.ext (map_smul _ c (y : ℂ_[p] ⊗[ℚ_[p]] V))

/-- `hodgeTateInclusion ρ K i y` is the image `y tⁱ` of `y` under `c ⊗ v ↦ c tⁱ ⊗ v`. -/
@[simp]
theorem coe_hodgeTateInclusion (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (i : ℤ) (y : ρ.twistPeriods K i) :
    (hodgeTateInclusion ρ K i y : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) =
      LinearMap.rTensor V (AddMonoidAlgebra.lsingle (R := ℚ_[p]) i) y :=
  rfl

/-- **The graded decomposition, by inclusions**: the `ℚ_p`-linear map
`⨁ᵢ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K} → D_HT(V)` induced by the inclusions `y ↦ y tⁱ` of the degrees is
bijective. -/
theorem bijective_toModule_hodgeTateInclusion (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Bijective (DirectSum.toModule ℚ_[p] ℤ _ (hodgeTateInclusion ρ K)) :=
  bijective_toModule fun i j _ => hodgeTateComponent_rTensor_lsingle i j _

/-- **The graded decomposition `D_HT(V) = ⨁ᵢ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`** (Fontaine–Ouyang, after
Proposition 6.5; Fontaine, Astérisque 223, Exposé III, §3.7 p. 141), as an isomorphism of
`ℚ_p`-vector spaces sending `x` to its components
(`Representation.coe_periodsHodgeTateEquiv_apply`), which are `ℂ_p`-linear
(`Representation.hodgeTateComponent_C_smul`). -/
def periodsHodgeTateEquiv (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup ≃ₗ[ℚ_[p]]
      ⨁ i, ρ.twistPeriods K i :=
  (LinearEquiv.ofBijective _ (bijective_toModule_hodgeTateInclusion ρ K)).symm

/-- The component of degree `i` of `periodsHodgeTateEquiv ρ K x` is that of `x`. -/
theorem coe_periodsHodgeTateEquiv_apply (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) (i : ℤ) :
    (periodsHodgeTateEquiv ρ K x i : ℂ_[p] ⊗[ℚ_[p]] V) = hodgeTateComponent p V i x := by
  obtain ⟨y, rfl⟩ := (periodsHodgeTateEquiv ρ K).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, periodsHodgeTateEquiv, LinearEquiv.symm_symm,
    LinearEquiv.ofBijective_apply]
  exact (hodgeTateComponent_toModule (fun i j _ => hodgeTateComponent_rTensor_lsingle i j _)
    y i).symm

/-- **The components are `ℂ_p`-linear**: the component of degree `i` of `C(c) x` is `c` times the
component of degree `i` of `x`, for `c ∈ ℂ_p`. In particular, for `c ∈ K`, the decomposition
`Representation.periodsHodgeTateEquiv` takes the action of `c ∈ B_HT^{G_K}` on `D_HT(V)` to the
action of `c ∈ ℂ_p^{G_K}` on each `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`. -/
theorem hodgeTateComponent_C_smul (i : ℤ) (c : ℂ_[p]) (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V) :
    hodgeTateComponent p V i (C c • x) = c • hodgeTateComponent p V i x := by
  induction x using TensorProduct.inductionOn with
  | tmul f v =>
    rw [TensorProduct.smul_tmul', hodgeTateComponent_tmul, hodgeTateComponent_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The `R`-dimension of a direct sum of finite free `R`-modules `M i` that vanish for `i ∉ s` is
the sum over `s` of the dimensions of the `M i`. -/
private theorem finrank_directSum_eq_sum {R ι : Type*} [Ring R] [StrongRankCondition R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] (s : Finset ι) (h : ∀ i ∉ s, ∀ x : M i, x = 0) :
    Module.finrank R (⨁ i, M i) = ∑ i ∈ s, Module.finrank R (M i) := by
  classical
  let f : (⨁ i, M i) →ₗ[R] ∀ i : s, M i := LinearMap.pi fun i => DirectSum.component R ι M i
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun y hy => DirectSum.ext_iff.2 fun i => ?_,
      fun z => ⟨DFinsupp.mk s z, funext fun i => DFinsupp.mk_of_mem i.2⟩⟩
    by_cases hi : i ∈ s
    · exact congrFun hy ⟨i, hi⟩
    · exact h i hi _
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_coe_sort s fun i => Module.finrank R (M i)]

section FiniteDimensional

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (ρ : Representation ℚ_[p] (Galois p) V) [FiniteDimensional ℚ_[p] V]

/-- For `K` finite over `ℚ_p` and a finite-dimensional `V`, `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K} = 0` for all
but finitely many `i`: the components of a finite `ℚ_p`-spanning set of `D_HT(V)` vanish outside
a finite set of degrees, and `y tⁱ ∈ D_HT(V)` for `y ∈ (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`. -/
private theorem exists_finset_twistPeriods_eq_bot :
    ∃ s : Finset ℤ, ∀ i ∉ s, ρ.twistPeriods K i = ⊥ := by
  have hB := PadicComplex.isRegularPeriodRing_hodgeTateAction p K
  have : Module.Finite ℚ_[p]
      (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p) K.fixingSubgroup) :=
    Module.Finite.equiv (PadicComplex.hodgeTateFixedSubalgebraEquiv p K).toLinearEquiv
  have := hB.finite_periods ρ
  have : Module.Finite ℚ_[p] (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) :=
    Module.Finite.trans
      (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p) K.fixingSubgroup) _
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℚ_[p])
    (M := ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup)
  refine ⟨t.biUnion fun x =>
    (finite_support_hodgeTateComponent (x : ℂ_[p][T;T⁻¹] ⊗[ℚ_[p]] V)).toFinset,
    fun i hi => ?_⟩
  have h0 (x : ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) :
      hodgeTateComponent p V i x = 0 := by
    have hx : x ∈ Submodule.span ℚ_[p] (t : Set _) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      by_contra h
      exact hi (Finset.mem_biUnion.2 ⟨x, hx, (Set.Finite.mem_toFinset _).2 h⟩)
    | zero => rw [ZeroMemClass.coe_zero, map_zero]
    | add x y _ _ hx hy => rw [Submodule.coe_add, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Submodule.coe_smul_of_tower, map_smul, hx, smul_zero]
  refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
  have := h0 ⟨_, rTensor_lsingle_mem_periods_hodgeTateAction hy⟩
  simpa only [hodgeTateComponent_rTensor_lsingle, ↓reduceIte] using this

/-- Only finitely many Hodge–Tate numbers of a finite-dimensional `V` over `K` are nonzero, for
`K` finite over `ℚ_p` inside `ℚ̄_p`. -/
theorem finite_support_hodgeTateNumber : (Function.support (ρ.hodgeTateNumber K)).Finite := by
  obtain ⟨s, hs⟩ := exists_finset_twistPeriods_eq_bot K ρ
  refine (Set.Finite.preimage neg_injective.injOn s.finite_toSet).subset fun i hi => ?_
  by_contra h
  exact hi (by rw [hodgeTateNumber, hs (-i) h, finrank_bot])

/-- **`dim_K D_HT(V) = Σᵢ hᵢ`**: for `K` finite over `ℚ_p` and a finite-dimensional `V`, the
dimension of `D_HT(V)` over `B_HT^{G_K} = K` is the sum of the Hodge–Tate numbers of `V`. -/
theorem finrank_periods_hodgeTateAction_eq_finsum :
    Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p)
      K.fixingSubgroup) (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) =
      ∑ᶠ i, ρ.hodgeTateNumber K i := by
  obtain ⟨s, hs⟩ := exists_finset_twistPeriods_eq_bot K ρ
  have hB := PadicComplex.isRegularPeriodRing_hodgeTateAction p K
  have hC := isRegularPeriodRing_of_isField (Field.toIsField ℂ_[p]) (PadicComplex.galoisAlgHom p)
    K.fixingSubgroup
  have := hB.finite_periods ρ
  have := hB.free_periods ρ
  have : Module.Finite ℚ_[p]
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup) :=
    Module.Finite.equiv (PadicComplex.galoisFixedSubalgebraEquiv p K).toLinearEquiv
  have hWfin (i : ℤ) : Module.Finite
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i) :=
    hC.finite_periods (ρ.tateTwist i)
  have hWfree (i : ℤ) : Module.Free
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i) :=
    hC.free_periods (ρ.tateTwist i)
  have hWfin' (i : ℤ) : Module.Finite ℚ_[p] (ρ.twistPeriods K i) :=
    Module.Finite.trans (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup) _
  have hdB : Module.finrank ℚ_[p]
      (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p) K.fixingSubgroup) =
      Module.finrank ℚ_[p] K :=
    (PadicComplex.hodgeTateFixedSubalgebraEquiv p K).toLinearEquiv.finrank_eq.symm
  have hdC : Module.finrank ℚ_[p]
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup) =
      Module.finrank ℚ_[p] K :=
    (PadicComplex.galoisFixedSubalgebraEquiv p K).toLinearEquiv.finrank_eq.symm
  have hsum : Module.finrank ℚ_[p] (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) =
      ∑ i ∈ s, Module.finrank ℚ_[p] (ρ.twistPeriods K i) := by
    rw [(periodsHodgeTateEquiv ρ K).finrank_eq]
    exact finrank_directSum_eq_sum s fun i hi y =>
      Subtype.ext ((Submodule.eq_bot_iff _).1 (hs i hi) y y.2)
  have hsupp : (Function.support fun i => Module.finrank
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i)) ⊆ s := fun i hi => by
    by_contra h
    exact hi (by beta_reduce; rw [hs i h, finrank_bot])
  have hfs : ∑ᶠ i, ρ.hodgeTateNumber K i = ∑ i ∈ s, Module.finrank
      (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ρ.twistPeriods K i) := by
    rw [← finsum_eq_sum_of_support_subset _ hsupp, ← finsum_comp_equiv (Equiv.neg ℤ)
      (f := fun i => Module.finrank
        (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
        (ρ.twistPeriods K i))]
    rw [Equiv.neg_apply]
    rfl
  rw [hfs]
  refine Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ_[p]) (M := K)) ?_
  rw [← hdB, Module.finrank_mul_finrank, hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hdB, ← hdC, Module.finrank_mul_finrank]

/-- **`Σᵢ hᵢ ≤ dim_{ℚ_p} V`**, for `K` finite over `ℚ_p` and a finite-dimensional `V`. -/
theorem finsum_hodgeTateNumber_le : ∑ᶠ i, ρ.hodgeTateNumber K i ≤ Module.finrank ℚ_[p] V := by
  rw [← finrank_periods_hodgeTateAction_eq_finsum K ρ]
  exact finrank_periods_hodgeTateAction_le K ρ

/-- **`V` is Hodge–Tate if and only if `Σᵢ hᵢ = dim_{ℚ_p} V`** (Fontaine–Ouyang, §6.1), for `K`
finite over `ℚ_p` and a finite-dimensional `V`. -/
theorem isHodgeTate_iff_finsum_hodgeTateNumber :
    ρ.IsHodgeTate K ↔ ∑ᶠ i, ρ.hodgeTateNumber K i = Module.finrank ℚ_[p] V := by
  rw [IsHodgeTate, IsAdmissible, finrank_periods_hodgeTateAction_eq_finsum K ρ,
    and_iff_right ‹_›]

end FiniteDimensional

end Representation
