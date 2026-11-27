/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.WeaklyAdmissible
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Direct sums of filtered `(φ, N)`-modules

Let `K₀` be a field with a ring automorphism `σ`, let `p ∈ K₀` and let `K` be a field extension
of `K₀`. The direct sum of two `(φ, N)`-modules `D₁` and `D₂` over `K₀` is `D₁ × D₂`, on which `φ`
and `N` act componentwise. For filtered `(φ, N)`-modules, the filtration of
`(D₁ × D₂)_K = K ⊗_{K₀} (D₁ × D₂)` is the product filtration `Fil^i D₁_K × Fil^i D₂_K`,
transported along the isomorphism `(D₁ × D₂)_K ≅ D₁_K × D₂_K` (`TensorProduct.prodRight`).

The Hodge number `t_H` and the Newton number `t_N` are additive in direct sums, the inclusions
and projections are morphisms of filtered `(φ, N)`-modules, and the direct sum of two weakly
admissible filtered `(φ, N)`-modules is weakly admissible. This is the additive part of the
statement that the weakly admissible filtered `(φ, N)`-modules form an abelian category
(Fontaine–Ouyang, Proposition 8.41); kernels, images and cokernels are treated in
`MathlibExt.RingTheory.PhiNModule.WeaklyAdmissible`.

## Main definitions

* `PhiNModule.prod`: the direct sum of two `(φ, N)`-modules.
* `PhiNModule.inl`, `PhiNModule.inr`, `PhiNModule.fst`, `PhiNModule.snd`: the inclusions and the
  projections, as morphisms of `(φ, N)`-modules.
* `DecreasingFiltration.prod`: the product filtration `Fil^i (V × W) = Fil^i V × Fil^i W`.
* `FilteredPhiNModule.prod`: the direct sum of two filtered `(φ, N)`-modules.
* `FilteredPhiNModule.inl`, `FilteredPhiNModule.inr`, `FilteredPhiNModule.fst`,
  `FilteredPhiNModule.snd`: the inclusions and the projections, as morphisms of filtered
  `(φ, N)`-modules.

## Main results

* `PhiNModule.Hom.isStable_comap`, `PhiNModule.Hom.isStable_map`: preimages and images of
  stable subspaces under morphisms are stable.
* `DecreasingFiltration.hodgeNumber_prod`, `FilteredPhiNModule.hodgeNumber_prod`: additivity of
  `t_H` in direct sums.
* `PhiNModule.newtonNumber_prod`, `FilteredPhiNModule.newtonNumber_prod`: additivity of `t_N` in
  direct sums.
* `FilteredPhiNModule.IsWeaklyAdmissible.prod`: the direct sum of two weakly admissible filtered
  `(φ, N)`-modules is weakly admissible.

## Implementation notes

For a stable subspace `D' ⊆ D₁ × D₂`, let `D'₁ = {x ∈ D₁ | (x, 0) ∈ D'}` and let `D'₂ ⊆ D₂` be the
image of `D'` under the second projection. Both are stable, and `0 → D'₁ → D' → D'₂ → 0` is exact,
so `t_N(D') = t_N(D'₁) + t_N(D'₂)`. The filtration induced on `D'₁_K` from `D'_K` is the one
induced from `D₁_K`, and as the second projection maps the filtration of `(D₁ × D₂)_K` into that
of `D₂_K`, the quotient filtration on `D'₂_K` is contained in the one induced from `D₂_K`. Hence
`t_H(D') ≤ t_H(D'₁) + t_H(D'₂)`, and the weak admissibility of `D₁` and `D₂` gives
`t_H(D') ≤ t_N(D')`.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.5, Proposition 8.41.
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.4.4 p. 151.
-/

@[expose] public section

open TensorProduct

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀}

namespace PhiNModule

variable {D₁ D₂ : Type*} [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂]
  (M₁ : PhiNModule σ p D₁) (M₂ : PhiNModule σ p D₂)

/-- The direct sum of a `(φ, N)`-module `M₁` on `D₁` and a `(φ, N)`-module `M₂` on `D₂`: the
`(φ, N)`-module on `D₁ × D₂` on which `φ` and `N` act componentwise,
`φ (x₁, x₂) = (φ x₁, φ x₂)` and `N (x₁, x₂) = (N x₁, N x₂)`. -/
def prod : PhiNModule σ p (D₁ × D₂) where
  φ := { M₁.φ.toAddEquiv.prodCongr M₂.φ.toAddEquiv with
    map_smul' a x := Prod.ext (M₁.φ.map_smulₛₗ a x.1) (M₂.φ.map_smulₛₗ a x.2) }
  N := M₁.N.prodMap M₂.N
  N_φ x := Prod.ext (M₁.N_φ x.1) (M₂.N_φ x.2)

/-- The Frobenius of the direct sum `D₁ × D₂` acts componentwise:
`φ (x₁, x₂) = (φ x₁, φ x₂)`. -/
@[simp]
theorem prod_φ_apply (x : D₁ × D₂) : (M₁.prod M₂).φ x = (M₁.φ x.1, M₂.φ x.2) :=
  rfl

/-- The monodromy operator of the direct sum `D₁ × D₂` acts componentwise:
`N (x₁, x₂) = (N x₁, N x₂)`. -/
@[simp]
theorem prod_N_apply (x : D₁ × D₂) : (M₁.prod M₂).N x = (M₁.N x.1, M₂.N x.2) :=
  rfl

/-- The inclusion `x ↦ (x, 0)` of `D₁` into the direct sum `D₁ × D₂`, as a morphism of
`(φ, N)`-modules from `M₁` to `M₁.prod M₂`. -/
def inl : M₁.Hom (M₁.prod M₂) where
  toLinearMap := LinearMap.inl K₀ D₁ D₂
  map_φ _ := Prod.ext rfl (map_zero M₂.φ).symm
  map_N _ := Prod.ext rfl (map_zero M₂.N).symm

/-- The inclusion `x ↦ (0, x)` of `D₂` into the direct sum `D₁ × D₂`, as a morphism of
`(φ, N)`-modules from `M₂` to `M₁.prod M₂`. -/
def inr : M₂.Hom (M₁.prod M₂) where
  toLinearMap := LinearMap.inr K₀ D₁ D₂
  map_φ _ := Prod.ext (map_zero M₁.φ).symm rfl
  map_N _ := Prod.ext (map_zero M₁.N).symm rfl

/-- The projection `(x₁, x₂) ↦ x₁` of the direct sum `D₁ × D₂` onto `D₁`, as a morphism of
`(φ, N)`-modules from `M₁.prod M₂` to `M₁`. -/
def fst : (M₁.prod M₂).Hom M₁ where
  toLinearMap := LinearMap.fst K₀ D₁ D₂
  map_φ _ := rfl
  map_N _ := rfl

/-- The projection `(x₁, x₂) ↦ x₂` of the direct sum `D₁ × D₂` onto `D₂`, as a morphism of
`(φ, N)`-modules from `M₁.prod M₂` to `M₂`. -/
def snd : (M₁.prod M₂).Hom M₂ where
  toLinearMap := LinearMap.snd K₀ D₁ D₂
  map_φ _ := rfl
  map_N _ := rfl

/-- The linear map underlying `PhiNModule.inl M₁ M₂` is `LinearMap.inl`, `x ↦ (x, 0)`. -/
@[simp]
theorem inl_toLinearMap : (inl M₁ M₂).toLinearMap = LinearMap.inl K₀ D₁ D₂ :=
  rfl

/-- The linear map underlying `PhiNModule.inr M₁ M₂` is `LinearMap.inr`, `x ↦ (0, x)`. -/
@[simp]
theorem inr_toLinearMap : (inr M₁ M₂).toLinearMap = LinearMap.inr K₀ D₁ D₂ :=
  rfl

/-- The linear map underlying `PhiNModule.fst M₁ M₂` is `LinearMap.fst`, `(x₁, x₂) ↦ x₁`. -/
@[simp]
theorem fst_toLinearMap : (fst M₁ M₂).toLinearMap = LinearMap.fst K₀ D₁ D₂ :=
  rfl

/-- The linear map underlying `PhiNModule.snd M₁ M₂` is `LinearMap.snd`, `(x₁, x₂) ↦ x₂`. -/
@[simp]
theorem snd_toLinearMap : (snd M₁ M₂).toLinearMap = LinearMap.snd K₀ D₁ D₂ :=
  rfl

variable {M₁ M₂}

/-- The preimage `f⁻¹(D')` of a stable subspace `D' ⊆ D₂` under a morphism of `(φ, N)`-modules
`f : M₁ → M₂` is a stable subspace of `D₁`. -/
theorem Hom.isStable_comap (f : M₁.Hom M₂) {D' : Submodule K₀ D₂} (h : M₂.IsStable D') :
    M₁.IsStable (D'.comap f.toLinearMap) where
  φ_mem hx := by
    rw [Submodule.mem_comap, f.map_φ]
    exact h.φ_mem hx
  N_mem hx := by
    rw [Submodule.mem_comap, f.map_N]
    exact h.N_mem hx

/-- The image `f(D')` of a stable subspace `D' ⊆ D₁` under a morphism of `(φ, N)`-modules
`f : M₁ → M₂` is a stable subspace of `D₂`. -/
theorem Hom.isStable_map (f : M₁.Hom M₂) {D' : Submodule K₀ D₁} (h : M₁.IsStable D') :
    M₂.IsStable (D'.map f.toLinearMap) where
  φ_mem := by
    rintro - ⟨x, hx, rfl⟩
    exact ⟨M₁.φ x, h.φ_mem hx, f.map_φ x⟩
  N_mem := by
    rintro - ⟨x, hx, rfl⟩
    exact ⟨M₁.N x, h.N_mem hx, f.map_N x⟩

/-- Additivity of the Newton number in direct sums: for an additive valuation
`v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x` and finite-dimensional
`(φ, N)`-modules `M₁` on `D₁` and `M₂` on `D₂`, the Newton number of the direct sum on `D₁ × D₂`
is the sum of the Newton numbers of `M₁` and `M₂`. -/
theorem newtonNumber_prod (v : AddValuation K₀ (WithTop ℤ)) (hv : ∀ x, v (σ x) = v x)
    (M₁ : PhiNModule σ p D₁) (M₂ : PhiNModule σ p D₂) [FiniteDimensional K₀ D₁]
    [FiniteDimensional K₀ D₂] :
    (M₁.prod M₂).newtonNumber v = M₁.newtonNumber v + M₂.newtonNumber v :=
  newtonNumber_eq_add_of_exact v hv LinearMap.inl_injective LinearMap.snd_surjective
    Function.Exact.inl_snd (inl M₁ M₂).map_φ (snd M₁ M₂).map_φ

end PhiNModule

namespace DecreasingFiltration

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- The product of a filtration `F` of `V` and a filtration `G` of `W`: the filtration of `V × W`
with `Fil^i (V × W) = Fil^i V × Fil^i W`. -/
def prod (F : DecreasingFiltration K V) (G : DecreasingFiltration K W) :
    DecreasingFiltration K (V × W) where
  Fil i := (F.Fil i).prod (G.Fil i)
  antitone _ _ hij := Submodule.prod_mono (F.antitone hij) (G.antitone hij)
  iInf_eq_bot := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Submodule.mem_iInf] at hx
    have h₁ : x.1 ∈ ⨅ i, F.Fil i := (Submodule.mem_iInf _).2 fun i => (hx i).1
    have h₂ : x.2 ∈ ⨅ i, G.Fil i := (Submodule.mem_iInf _).2 fun i => (hx i).2
    rw [F.iInf_eq_bot, Submodule.mem_bot] at h₁
    rw [G.iInf_eq_bot, Submodule.mem_bot] at h₂
    exact (Submodule.mem_bot K).2 (Prod.ext h₁ h₂)
  iSup_eq_top := by
    refine eq_top_iff.2 fun x _ => ?_
    have h₁ : x.1 ∈ ⨆ i, F.Fil i := by
      rw [F.iSup_eq_top]
      exact Submodule.mem_top
    have h₂ : x.2 ∈ ⨆ i, G.Fil i := by
      rw [G.iSup_eq_top]
      exact Submodule.mem_top
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ F.antitone.directed_le).1 h₁
    obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ G.antitone.directed_le).1 h₂
    exact Submodule.mem_iSup_of_mem (min i j)
      ⟨F.antitone (min_le_left i j) hi, G.antitone (min_le_right i j) hj⟩

/-- The `i`-th step of the product filtration of `V × W` is `Fil^i V × Fil^i W`. -/
@[simp]
theorem prod_fil (F : DecreasingFiltration K V) (G : DecreasingFiltration K W) (i : ℤ) :
    (F.prod G).Fil i = (F.Fil i).prod (G.Fil i) :=
  rfl

/-- For a filtration `F` of a finite-dimensional space `V` and a filtration `G` of a
finite-dimensional space `W`, the product filtration of `V × W` has Hodge number
`t_H(F) + t_H(G)`. -/
theorem hodgeNumber_prod [FiniteDimensional K V] [FiniteDimensional K W]
    (F : DecreasingFiltration K V) (G : DecreasingFiltration K W) :
    (F.prod G).hodgeNumber = F.hodgeNumber + G.hodgeNumber := by
  have h₁ : (F.prod G).comap (LinearMap.inl K V W) LinearMap.inl_injective = F :=
    ext fun _ => Submodule.prod_comap_inl _ _
  have h₂ : (F.prod G).map (LinearMap.snd K V W) LinearMap.snd_surjective = G :=
    ext fun _ => Submodule.prod_map_snd _ _
  rw [(F.prod G).hodgeNumber_eq_add_of_exact LinearMap.inl_injective LinearMap.snd_surjective
    Function.Exact.inl_snd, h₁, h₂]

end DecreasingFiltration

namespace FilteredPhiNModule

variable {K : Type*} [Field K] [Algebra K₀ K] {D₁ D₂ : Type*} [AddCommGroup D₁] [Module K₀ D₁]
  [AddCommGroup D₂] [Module K₀ D₂] (M₁ : FilteredPhiNModule σ p K D₁)
  (M₂ : FilteredPhiNModule σ p K D₂)

/-- The direct sum of a filtered `(φ, N)`-module `M₁` on `D₁` and a filtered `(φ, N)`-module `M₂`
on `D₂`: the direct sum `D₁ × D₂` of the underlying `(φ, N)`-modules (`PhiNModule.prod`), with the
filtration of `(D₁ × D₂)_K = K ⊗_{K₀} (D₁ × D₂)` whose `i`-th step is the preimage of
`Fil^i D₁_K × Fil^i D₂_K` under the isomorphism `(D₁ × D₂)_K ≅ D₁_K × D₂_K`
(`TensorProduct.prodRight`). -/
def prod : FilteredPhiNModule σ p K (D₁ × D₂) where
  toPhiNModule := M₁.toPhiNModule.prod M₂.toPhiNModule
  fil := (M₁.fil.prod M₂.fil).comap (prodRight K₀ K K D₁ D₂ : K ⊗[K₀] (D₁ × D₂) →ₗ[K] _)
    (LinearEquiv.injective _)

/-- The `(φ, N)`-module underlying the direct sum of two filtered `(φ, N)`-modules is the direct
sum of the underlying `(φ, N)`-modules. -/
@[simp]
theorem prod_toPhiNModule :
    (M₁.prod M₂).toPhiNModule = M₁.toPhiNModule.prod M₂.toPhiNModule :=
  rfl

/-- The `i`-th step of the filtration of the direct sum `D₁ × D₂` is the preimage of
`Fil^i D₁_K × Fil^i D₂_K` under the isomorphism `(D₁ × D₂)_K ≅ D₁_K × D₂_K`
(`TensorProduct.prodRight`). -/
theorem prod_fil_fil (i : ℤ) : (M₁.prod M₂).fil.Fil i =
    ((M₁.fil.Fil i).prod (M₂.fil.Fil i)).comap
      (prodRight K₀ K K D₁ D₂ : K ⊗[K₀] (D₁ × D₂) →ₗ[K] _) :=
  rfl

/-- The isomorphism `(D₁ × D₂)_K ≅ D₁_K × D₂_K` is given by the base changes of the two
projections. -/
private theorem prodRight_apply (y : K ⊗[K₀] (D₁ × D₂)) :
    prodRight K₀ K K D₁ D₂ y =
      ((LinearMap.fst K₀ D₁ D₂).baseChange K y, (LinearMap.snd K₀ D₁ D₂).baseChange K y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => simp
  | add y z hy hz => simp [hy, hz]

/-- A vector `y` of `(D₁ × D₂)_K` lies in the `i`-th step of the filtration of the direct sum
`D₁ × D₂` if and only if its images under the base changes `(D₁ × D₂)_K → D₁_K` and
`(D₁ × D₂)_K → D₂_K` of the two projections lie in `Fil^i D₁_K` and in `Fil^i D₂_K`. -/
theorem mem_prod_fil_iff {i : ℤ} {y : K ⊗[K₀] (D₁ × D₂)} :
    y ∈ (M₁.prod M₂).fil.Fil i ↔ (LinearMap.fst K₀ D₁ D₂).baseChange K y ∈ M₁.fil.Fil i ∧
      (LinearMap.snd K₀ D₁ D₂).baseChange K y ∈ M₂.fil.Fil i := by
  rw [prod_fil_fil, Submodule.mem_comap, LinearEquiv.coe_coe, prodRight_apply, Submodule.mem_prod]

/-- Additivity of the Hodge number in direct sums: for finite-dimensional filtered
`(φ, N)`-modules `M₁` on `D₁` and `M₂` on `D₂`, the Hodge number of the direct sum on `D₁ × D₂`
is the sum of the Hodge numbers of `M₁` and `M₂`. -/
theorem hodgeNumber_prod [FiniteDimensional K₀ D₁] [FiniteDimensional K₀ D₂] :
    (M₁.prod M₂).hodgeNumber = M₁.hodgeNumber + M₂.hodgeNumber :=
  ((M₁.fil.prod M₂.fil).hodgeNumber_comap_linearEquiv (prodRight K₀ K K D₁ D₂)).trans
    (M₁.fil.hodgeNumber_prod M₂.fil)

/-- Additivity of the Newton number in direct sums: for an additive valuation
`v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x` and finite-dimensional
filtered `(φ, N)`-modules `M₁` on `D₁` and `M₂` on `D₂`, the Newton number of the direct sum on
`D₁ × D₂` is the sum of the Newton numbers of `M₁` and `M₂`. -/
theorem newtonNumber_prod {v : AddValuation K₀ (WithTop ℤ)} (hv : ∀ x, v (σ x) = v x)
    [FiniteDimensional K₀ D₁] [FiniteDimensional K₀ D₂] :
    (M₁.prod M₂).newtonNumber v = M₁.newtonNumber v + M₂.newtonNumber v :=
  PhiNModule.newtonNumber_prod v hv M₁.toPhiNModule M₂.toPhiNModule

/-! ### The inclusions and the projections -/

/-- The inclusion `x ↦ (x, 0)` of `D₁` into the direct sum `D₁ × D₂`, as a morphism of filtered
`(φ, N)`-modules from `M₁` to `M₁.prod M₂`: its base change maps `Fil^i D₁_K` into the `i`-th step
of the filtration of `(D₁ × D₂)_K`. -/
def inl : M₁.Hom (M₁.prod M₂) where
  toHom := PhiNModule.inl M₁.toPhiNModule M₂.toPhiNModule
  map_fil_le _ := by
    rintro - ⟨x, hx, rfl⟩
    rw [mem_prod_fil_iff, PhiNModule.inl_toLinearMap, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, LinearMap.fst_comp_inl, LinearMap.baseChange_id,
      LinearMap.id_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.snd_comp_inl, LinearMap.baseChange_zero, LinearMap.zero_apply]
    exact ⟨hx, zero_mem _⟩

/-- The inclusion `x ↦ (0, x)` of `D₂` into the direct sum `D₁ × D₂`, as a morphism of filtered
`(φ, N)`-modules from `M₂` to `M₁.prod M₂`: its base change maps `Fil^i D₂_K` into the `i`-th step
of the filtration of `(D₁ × D₂)_K`. -/
def inr : M₂.Hom (M₁.prod M₂) where
  toHom := PhiNModule.inr M₁.toPhiNModule M₂.toPhiNModule
  map_fil_le _ := by
    rintro - ⟨x, hx, rfl⟩
    rw [mem_prod_fil_iff, PhiNModule.inr_toLinearMap, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, LinearMap.fst_comp_inr, LinearMap.baseChange_zero,
      LinearMap.zero_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.snd_comp_inr, LinearMap.baseChange_id, LinearMap.id_apply]
    exact ⟨zero_mem _, hx⟩

/-- The projection `(x₁, x₂) ↦ x₁` of the direct sum `D₁ × D₂` onto `D₁`, as a morphism of
filtered `(φ, N)`-modules from `M₁.prod M₂` to `M₁`: its base change maps the `i`-th step of the
filtration of `(D₁ × D₂)_K` into `Fil^i D₁_K`. -/
def fst : (M₁.prod M₂).Hom M₁ where
  toHom := PhiNModule.fst M₁.toPhiNModule M₂.toPhiNModule
  map_fil_le _ := by
    rintro - ⟨y, hy, rfl⟩
    exact ((M₁.mem_prod_fil_iff M₂).1 hy).1

/-- The projection `(x₁, x₂) ↦ x₂` of the direct sum `D₁ × D₂` onto `D₂`, as a morphism of
filtered `(φ, N)`-modules from `M₁.prod M₂` to `M₂`: its base change maps the `i`-th step of the
filtration of `(D₁ × D₂)_K` into `Fil^i D₂_K`. -/
def snd : (M₁.prod M₂).Hom M₂ where
  toHom := PhiNModule.snd M₁.toPhiNModule M₂.toPhiNModule
  map_fil_le _ := by
    rintro - ⟨y, hy, rfl⟩
    exact ((M₁.mem_prod_fil_iff M₂).1 hy).2

/-- The morphism of `(φ, N)`-modules underlying `FilteredPhiNModule.inl M₁ M₂` is
`PhiNModule.inl`. -/
@[simp]
theorem inl_toHom : (inl M₁ M₂).toHom = PhiNModule.inl M₁.toPhiNModule M₂.toPhiNModule :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `FilteredPhiNModule.inr M₁ M₂` is
`PhiNModule.inr`. -/
@[simp]
theorem inr_toHom : (inr M₁ M₂).toHom = PhiNModule.inr M₁.toPhiNModule M₂.toPhiNModule :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `FilteredPhiNModule.fst M₁ M₂` is
`PhiNModule.fst`. -/
@[simp]
theorem fst_toHom : (fst M₁ M₂).toHom = PhiNModule.fst M₁.toPhiNModule M₂.toPhiNModule :=
  rfl

/-- The morphism of `(φ, N)`-modules underlying `FilteredPhiNModule.snd M₁ M₂` is
`PhiNModule.snd`. -/
@[simp]
theorem snd_toHom : (snd M₁ M₂).toHom = PhiNModule.snd M₁.toPhiNModule M₂.toPhiNModule :=
  rfl

/-! ### Weak admissibility -/

section Stable

variable {M₁ M₂} {D' : Submodule K₀ (D₁ × D₂)}

/-- For a stable subspace `D'` of the direct sum, `{x ∈ D₁ | (x, 0) ∈ D'}` is stable. -/
private theorem isStable_comap_inl (h : (M₁.prod M₂).IsStable D') :
    M₁.IsStable (D'.comap (LinearMap.inl K₀ D₁ D₂)) :=
  (PhiNModule.inl M₁.toPhiNModule M₂.toPhiNModule).isStable_comap h

/-- For a stable subspace `D'` of the direct sum, its image in `D₂` is stable. -/
private theorem isStable_map_snd (h : (M₁.prod M₂).IsStable D') :
    M₂.IsStable (D'.map (LinearMap.snd K₀ D₁ D₂)) :=
  (PhiNModule.snd M₁.toPhiNModule M₂.toPhiNModule).isStable_map h

variable (D') in
/-- The inclusion `x ↦ (x, 0)` of `{x ∈ D₁ | (x, 0) ∈ D'}` into `D'`. -/
private def inlRestrict : D'.comap (LinearMap.inl K₀ D₁ D₂) →ₗ[K₀] D' :=
  (LinearMap.inl K₀ D₁ D₂).restrict fun _ hx => hx

variable (D') in
/-- The second projection of `D'` onto its image in `D₂`. -/
private def sndRestrict : D' →ₗ[K₀] D'.map (LinearMap.snd K₀ D₁ D₂) :=
  (LinearMap.snd K₀ D₁ D₂).restrict fun _ hx => Submodule.mem_map_of_mem hx

private theorem inlRestrict_injective : Function.Injective (inlRestrict D') := fun _ _ hxy =>
  Subtype.ext (LinearMap.inl_injective (congrArg Subtype.val hxy))

private theorem sndRestrict_surjective : Function.Surjective (sndRestrict D') := by
  rintro ⟨-, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

private theorem exact_inlRestrict_sndRestrict :
    Function.Exact (inlRestrict D') (sndRestrict D') := by
  intro y
  constructor
  · intro h
    have h₂ : (y : D₁ × D₂).2 = 0 := congrArg Subtype.val h
    refine ⟨⟨(y : D₁ × D₂).1, ?_⟩, Subtype.ext (Prod.ext rfl h₂.symm)⟩
    change ((y : D₁ × D₂).1, (0 : D₂)) ∈ D'
    rw [← h₂]
    exact y.2
  · rintro ⟨x, rfl⟩
    rfl

variable [FiniteDimensional K₀ D₁] [FiniteDimensional K₀ D₂]

/-- Additivity of `t_N` along `0 → {x ∈ D₁ | (x, 0) ∈ D'} → D' → pr₂(D') → 0`. -/
private theorem newtonNumber_restrict_prod {v : AddValuation K₀ (WithTop ℤ)}
    (hv : ∀ x, v (σ x) = v x) (h : (M₁.prod M₂).IsStable D') :
    ((M₁.prod M₂).restrict D' h).newtonNumber v =
      (M₁.restrict _ (isStable_comap_inl h)).newtonNumber v +
        (M₂.restrict _ (isStable_map_snd h)).newtonNumber v :=
  PhiNModule.newtonNumber_eq_add_of_exact v hv inlRestrict_injective sndRestrict_surjective
    exact_inlRestrict_sndRestrict
    (fun x => Subtype.ext ((PhiNModule.inl M₁.toPhiNModule M₂.toPhiNModule).map_φ x))
    fun _ => rfl

/-- Subadditivity of `t_H` along `0 → {x ∈ D₁ | (x, 0) ∈ D'} → D' → pr₂(D') → 0`: the filtration
induced on `{x ∈ D₁ | (x, 0) ∈ D'}_K` from `D'_K` is the one induced from `D₁_K`, and the quotient
filtration on `pr₂(D')_K` is contained in the one induced from `D₂_K`. -/
private theorem hodgeNumber_restrict_prod_le (h : (M₁.prod M₂).IsStable D') :
    ((M₁.prod M₂).restrict D' h).hodgeNumber ≤
      (M₁.restrict _ (isStable_comap_inl h)).hodgeNumber +
        (M₂.restrict _ (isStable_map_snd h)).hodgeNumber := by
  set D'₁ := D'.comap (LinearMap.inl K₀ D₁ D₂)
  set D'₂ := D'.map (LinearMap.snd K₀ D₁ D₂)
  have hf : Function.Injective ((inlRestrict D').baseChange K) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ inlRestrict_injective
  have hg : Function.Surjective ((sndRestrict D').baseChange K) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective K sndRestrict_surjective
  have hfg : Function.Exact ((inlRestrict D').baseChange K) ((sndRestrict D').baseChange K) := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact lTensor_exact K exact_inlRestrict_sndRestrict sndRestrict_surjective
  have key := ((M₁.prod M₂).restrict D' h).fil.hodgeNumber_eq_add_of_exact hf hg hfg
  have h₁ : ((M₁.prod M₂).restrict D' h).fil.comap ((inlRestrict D').baseChange K) hf =
      (M₁.restrict D'₁ (isStable_comap_inl h)).fil := by
    have e₁ : LinearMap.fst K₀ D₁ D₂ ∘ₗ D'.subtype ∘ₗ inlRestrict D' = D'₁.subtype :=
      LinearMap.ext fun _ => rfl
    have e₂ : LinearMap.snd K₀ D₁ D₂ ∘ₗ D'.subtype ∘ₗ inlRestrict D' = 0 :=
      LinearMap.ext fun _ => rfl
    refine DecreasingFiltration.ext fun i => Submodule.ext fun y => ?_
    have hy₁ := LinearMap.congr_fun (congrArg (LinearMap.baseChange K) e₁) y
    have hy₂ := LinearMap.congr_fun (congrArg (LinearMap.baseChange K) e₂) y
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.baseChange_zero,
      LinearMap.zero_apply] at hy₁ hy₂
    rw [DecreasingFiltration.comap_fil, restrict_fil_fil, restrict_fil_fil, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.mem_comap, mem_prod_fil_iff, hy₁, hy₂]
    exact and_iff_left (zero_mem _)
  have h₂ (i : ℤ) :
      (((M₁.prod M₂).restrict D' h).fil.map ((sndRestrict D').baseChange K) hg).Fil i ≤
        (M₂.restrict D'₂ (isStable_map_snd h)).fil.Fil i := by
    have e : D'₂.subtype ∘ₗ sndRestrict D' = LinearMap.snd K₀ D₁ D₂ ∘ₗ D'.subtype :=
      LinearMap.ext fun _ => rfl
    rw [DecreasingFiltration.map_fil, restrict_fil_fil, restrict_fil_fil,
      Submodule.map_le_iff_le_comap, ← Submodule.comap_comp, ← LinearMap.baseChange_comp, e,
      LinearMap.baseChange_comp, Submodule.comap_comp]
    exact Submodule.comap_mono (Submodule.map_le_iff_le_comap.mp ((snd M₁ M₂).map_fil_le i))
  have h₃ := DecreasingFiltration.hodgeNumber_le_of_le h₂
  simp only [hodgeNumber]
  rw [key, h₁]
  linarith

end Stable

variable {M₁ M₂} in
/-- The direct sum of two weakly admissible filtered `(φ, N)`-modules is weakly admissible: for an
additive valuation `v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x` and
finite-dimensional filtered `(φ, N)`-modules `M₁` on `D₁` and `M₂` on `D₂` that are weakly
admissible for `v`, the direct sum `M₁.prod M₂` on `D₁ × D₂` is weakly admissible for `v`. This is
the additive part of the statement that the weakly admissible filtered `(φ, N)`-modules form an
abelian category (Fontaine–Ouyang, Proposition 8.41; Fontaine, Exposé III, §4.4.4). -/
theorem IsWeaklyAdmissible.prod [FiniteDimensional K₀ D₁] [FiniteDimensional K₀ D₂]
    {v : AddValuation K₀ (WithTop ℤ)} (hv : ∀ x, v (σ x) = v x) (h₁ : M₁.IsWeaklyAdmissible v)
    (h₂ : M₂.IsWeaklyAdmissible v) : (M₁.prod M₂).IsWeaklyAdmissible v where
  hodgeNumber_eq_newtonNumber := by
    rw [hodgeNumber_prod, newtonNumber_prod _ _ hv, h₁.hodgeNumber_eq_newtonNumber,
      h₂.hodgeNumber_eq_newtonNumber]
  hodgeNumber_restrict_le D' h := by
    have hH := hodgeNumber_restrict_prod_le h
    have hN := newtonNumber_restrict_prod hv h
    have hle₁ := h₁.hodgeNumber_restrict_le _ (isStable_comap_inl h)
    have hle₂ := h₂.hodgeNumber_restrict_le _ (isStable_map_snd h)
    linarith

end FilteredPhiNModule
