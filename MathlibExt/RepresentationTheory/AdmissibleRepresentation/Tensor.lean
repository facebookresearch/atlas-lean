/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-!
# Admissible representations: tensor products

Let `F` be a field, `G` a group, `S` a commutative `F`-algebra with a family
`act : G → (S →ₐ[F] S)` of `F`-algebra maps, `H` a subgroup of `G`, `E = S^H` the ring of
invariants (`Representation.fixedSubalgebra`), and `ρ`, `σ` `F`-linear representations of `G` on
`V` and `W`, with modules `D_S(V) = (S ⊗_F V)^H` and `D_S(W) = (S ⊗_F W)^H`
(`Representation.periods`). This file constructs the natural map of J.-M. Fontaine,
*Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §1.3.4 p. 122,
`D_S(V) ⊗_E D_S(W) → D_S(V ⊗_F W)`, `x ⊗ y ↦ x · y` (`Representation.periodsTensor`), where
`ρ ⊗ σ` is the tensor product representation `Representation.tprod` and the product
`(S ⊗_F V) × (S ⊗_F W) → S ⊗_F (V ⊗_F W)`, `(a ⊗ v) · (b ⊗ w) = (a * b) ⊗ (v ⊗ w)`
(`Representation.tensorMul`), is `S`-bilinear and equivariant for the diagonal actions
(`Representation.map_tensorMul`).

For representations admissible in the basis form (`Representation.HasFixedBasis`), the products
`bᵢ · cⱼ` of `S`-bases `(bᵢ)` of `S ⊗_F V` and `(cⱼ)` of `S ⊗_F W` of `H`-fixed vectors form an
`S`-basis of `S ⊗_F (V ⊗_F W)` of `H`-fixed vectors, so `ρ ⊗ σ` is admissible in the basis form
(`Representation.HasFixedBasis.tprod`), and the natural map is an isomorphism of `E`-modules
(`Representation.HasFixedBasis.periodsTensor_bijective`,
`Representation.HasFixedBasis.periodsTensorEquiv`). This is the analogue, for the basis form of
admissibility, of Fontaine's statement for admissible representations (*op. cit.*, §1.5.3
pp. 124–125); it needs no regularity of `S`, the family `act` need not be an action, and `E` is
only a commutative ring.

For a regular ring `S` (`Representation.IsRegularPeriodRing`), admissibility is equivalent to its
basis form, so the tensor product of admissible representations is admissible and Fontaine's
natural map is an isomorphism (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, *op. cit.*,
Proposition 1.5.2 p. 124; `Representation.IsRegularPeriodRing.isAdmissible_tprod`,
`Representation.IsRegularPeriodRing.periodsTensor_bijective`).

As in Fontaine's §1, no topology is involved, and the continuity of the actions is never assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S V W : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V] [AddCommGroup W] [Module F W]

/-! ### The product `(S ⊗_F V) × (S ⊗_F W) → S ⊗_F (V ⊗_F W)` -/

variable (F S V W) in
/-- **The product `(S ⊗_F V) × (S ⊗_F W) → S ⊗_F (V ⊗_F W)`**: the `S`-bilinear map
`(a ⊗ v, b ⊗ w) ↦ (a * b) ⊗ (v ⊗ w)`, the curried inverse of the `S`-linear isomorphism
`S ⊗_F (V ⊗_F W) ≃ (S ⊗_F V) ⊗_S (S ⊗_F W)`
(`TensorProduct.AlgebraTensorModule.distribBaseChange`). -/
def tensorMul : (S ⊗[F] V) →ₗ[S] (S ⊗[F] W) →ₗ[S] S ⊗[F] (V ⊗[F] W) :=
  TensorProduct.curry
    (TensorProduct.AlgebraTensorModule.distribBaseChange F S V W).symm.toLinearMap

/-- The product of `x` and `y` is the image of `x ⊗ y` under the inverse of
`S ⊗_F (V ⊗_F W) ≃ (S ⊗_F V) ⊗_S (S ⊗_F W)`. -/
theorem tensorMul_apply (x : S ⊗[F] V) (y : S ⊗[F] W) :
    tensorMul F S V W x y =
      (TensorProduct.AlgebraTensorModule.distribBaseChange F S V W).symm (x ⊗ₜ y) :=
  rfl

/-- `(a ⊗ v) · (b ⊗ w) = (a * b) ⊗ (v ⊗ w)`. -/
@[simp]
theorem tensorMul_tmul (a b : S) (v : V) (w : W) :
    tensorMul F S V W (a ⊗ₜ v) (b ⊗ₜ w) = (a * b) ⊗ₜ (v ⊗ₜ w) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul F S v w a b

/-- **The product is equivariant**: the diagonal action of `g` on `S ⊗_F (V ⊗_F W)` for the tensor
product representation `ρ ⊗ σ` maps the product of `x` and `y` to the product of the diagonal
actions of `g` on `x` and on `y`. -/
theorem map_tensorMul (ρ : Representation F G V) (σ : Representation F G W)
    (act : G → S →ₐ[F] S) (g : G) (x : S ⊗[F] V) (y : S ⊗[F] W) :
    TensorProduct.map (act g).toLinearMap (ρ.tprod σ g) (tensorMul F S V W x y) =
      tensorMul F S V W (TensorProduct.map (act g).toLinearMap (ρ g) x)
        (TensorProduct.map (act g).toLinearMap (σ g) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | tmul b w =>
      rw [tensorMul_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        tensorMul_tmul, tprod_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_mul]
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
  | add x x' hx hx' =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hx', map_add, map_add, LinearMap.add_apply]

/-! ### Fontaine's natural map `D_S(V) ⊗_E D_S(W) → D_S(V ⊗_F W)` -/

section Periods

variable {ρ : Representation F G V} {σ : Representation F G W} {act : G → S →ₐ[F] S}
  {H : Subgroup G}

/-- The product of a vector of `D_S(V)` and a vector of `D_S(W)` lies in `D_S(V ⊗_F W)`. -/
theorem tensorMul_mem_periods {x : S ⊗[F] V} (hx : x ∈ ρ.periods act H) {y : S ⊗[F] W}
    (hy : y ∈ σ.periods act H) : tensorMul F S V W x y ∈ (ρ.tprod σ).periods act H :=
  mem_periods.2 fun g hg => by
    rw [map_tensorMul, mem_periods.1 hx g hg, mem_periods.1 hy g hg]

variable (ρ σ act H) in
/-- **Fontaine's natural map `D_S(V) ⊗_{S^H} D_S(W) → D_S(V ⊗_F W)`** (Fontaine, Exposé III,
§1.3.4 p. 122): the `S^H`-linear map sending `x ⊗ y` to the product of `x` and `y` in
`S ⊗_F (V ⊗_F W)`. -/
def periodsTensor :
    ρ.periods act H ⊗[fixedSubalgebra S act H] σ.periods act H →ₗ[fixedSubalgebra S act H]
      (ρ.tprod σ).periods act H :=
  LinearMap.codRestrict _
    (TensorProduct.lift (((tensorMul F S V W).restrictScalars₁₂ (fixedSubalgebra S act H)
      (fixedSubalgebra S act H)).compl₁₂ (ρ.periods act H).subtype (σ.periods act H).subtype))
    fun z => by
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact tensorMul_mem_periods x.2 y.2
      | add z z' hz hz' => rw [map_add]; exact add_mem hz hz'

/-- Fontaine's natural map sends `x ⊗ y` to the product of `x` and `y`. -/
@[simp]
theorem coe_periodsTensor_tmul (x : ρ.periods act H) (y : σ.periods act H) :
    (periodsTensor ρ σ act H (x ⊗ₜ y) : S ⊗[F] (V ⊗[F] W)) = tensorMul F S V W x y :=
  rfl

end Periods

/-! ### Tensor products in the basis form of admissibility -/

section FixedBasis

variable {ρ : Representation F G V} {σ : Representation F G W} {act : G → S →ₐ[F] S}
  {H : Subgroup G} {ι κ : Type*}

/-- The `S`-basis `(bᵢ · cⱼ)` of `S ⊗_F (V ⊗_F W)` given by `S`-bases `(bᵢ)` of `S ⊗_F V` and
`(cⱼ)` of `S ⊗_F W`. -/
private def tensorBasis (b : Module.Basis ι S (S ⊗[F] V)) (c : Module.Basis κ S (S ⊗[F] W)) :
    Module.Basis (ι × κ) S (S ⊗[F] (V ⊗[F] W)) :=
  (b.tensorProduct c).map (TensorProduct.AlgebraTensorModule.distribBaseChange F S V W).symm

/-- The vectors of `tensorBasis b c` are the products `bᵢ · cⱼ`. -/
private theorem tensorBasis_apply (b : Module.Basis ι S (S ⊗[F] V))
    (c : Module.Basis κ S (S ⊗[F] W)) (k : ι × κ) :
    tensorBasis b c k = tensorMul F S V W (b k.1) (c k.2) := by
  rw [tensorBasis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply', tensorMul_apply]

/-- The products `bᵢ · cⱼ` of `H`-fixed vectors are `H`-fixed. -/
private theorem tensorBasis_mem_periods {b : Module.Basis ι S (S ⊗[F] V)}
    {c : Module.Basis κ S (S ⊗[F] W)} (hb : ∀ i, b i ∈ ρ.periods act H)
    (hc : ∀ j, c j ∈ σ.periods act H) (k : ι × κ) :
    tensorBasis b c k ∈ (ρ.tprod σ).periods act H := by
  rw [tensorBasis_apply]
  exact tensorMul_mem_periods (hb k.1) (hc k.2)

/-- **Tensor products preserve the basis form of admissibility**: if `S ⊗_F V` and `S ⊗_F W` have
`S`-bases of `H`-fixed vectors, then `S ⊗_F (V ⊗_F W)` also has an `S`-basis of `H`-fixed vectors,
for the tensor product representation `ρ ⊗ σ`. The proof takes the products `bᵢ · cⱼ` of the two
bases. -/
theorem HasFixedBasis.tprod (hρ : ρ.HasFixedBasis act H) (hσ : σ.HasFixedBasis act H) :
    (ρ.tprod σ).HasFixedBasis act H := by
  obtain ⟨d, b, hb⟩ := hρ
  obtain ⟨e, c, hc⟩ := hσ
  refine ⟨d * e, (tensorBasis b c).reindex finProdFinEquiv, fun k => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact tensorBasis_mem_periods hb hc _

/-- **Fontaine's natural map is bijective in the basis form of admissibility** (the analogue of
Fontaine, Exposé III, §1.5.3 pp. 124–125): if `S ⊗_F V` and `S ⊗_F W` have `S`-bases `(bᵢ)` and
`(cⱼ)` of `H`-fixed vectors, then `D_S(V) ⊗_{S^H} D_S(W) → D_S(V ⊗_F W)` is bijective. The proof
shows that it maps the `S^H`-basis `(bᵢ ⊗ cⱼ)` to the `S^H`-basis `(bᵢ · cⱼ)`. -/
theorem HasFixedBasis.periodsTensor_bijective (hρ : ρ.HasFixedBasis act H)
    (hσ : σ.HasFixedBasis act H) : Function.Bijective (periodsTensor ρ σ act H) := by
  obtain ⟨d, b, hb⟩ := hρ
  obtain ⟨e, c, hc⟩ := hσ
  let B := (periodsBasis b hb).tensorProduct (periodsBasis c hc)
  let T := periodsBasis (tensorBasis b c) (tensorBasis_mem_periods hb hc)
  have : periodsTensor ρ σ act H = (B.equiv T (_root_.Equiv.refl _)).toLinearMap :=
    B.ext fun k => by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      refine Subtype.ext ?_
      rw [Module.Basis.tensorProduct_apply', coe_periodsTensor_tmul, coe_periodsBasis,
        coe_periodsBasis, _root_.Equiv.refl_apply, coe_periodsBasis, tensorBasis_apply]
  rw [this]
  exact (B.equiv T (_root_.Equiv.refl _)).bijective

/-- **Fontaine's isomorphism `D_S(V) ⊗_{S^H} D_S(W) ≃ D_S(V ⊗_F W)`** in the basis form of
admissibility: when `S ⊗_F V` and `S ⊗_F W` have `S`-bases of `H`-fixed vectors, the natural map
`periodsTensor ρ σ act H`, as an `S^H`-linear equivalence. -/
def HasFixedBasis.periodsTensorEquiv (hρ : ρ.HasFixedBasis act H)
    (hσ : σ.HasFixedBasis act H) :
    ρ.periods act H ⊗[fixedSubalgebra S act H] σ.periods act H ≃ₗ[fixedSubalgebra S act H]
      (ρ.tprod σ).periods act H :=
  LinearEquiv.ofBijective (periodsTensor ρ σ act H) (hρ.periodsTensor_bijective hσ)

/-- The isomorphism `periodsTensorEquiv` applied to `z` is the natural map `periodsTensor` applied
to `z`. -/
@[simp]
theorem HasFixedBasis.periodsTensorEquiv_apply (hρ : ρ.HasFixedBasis act H)
    (hσ : σ.HasFixedBasis act H)
    (z : ρ.periods act H ⊗[fixedSubalgebra S act H] σ.periods act H) :
    hρ.periodsTensorEquiv hσ z = periodsTensor ρ σ act H z :=
  rfl

end FixedBasis

/-! ### Regular rings -/

section Regular

variable [IsDomain S] {ρ : Representation F G V} {σ : Representation F G W}
  {act : G →* (S →ₐ[F] S)} {H : Subgroup G}

/-- **Tensor products of admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Exposé III, Proposition 1.5.2 p. 124 and §1.5.3 pp. 124–125): for a regular ring `S`, if
`V` and `W` are admissible, then so is `V ⊗_F W`. -/
theorem IsRegularPeriodRing.isAdmissible_tprod (hS : IsRegularPeriodRing act H)
    (hρ : ρ.IsAdmissible act H) (hσ : σ.IsAdmissible act H) : (ρ.tprod σ).IsAdmissible act H := by
  have := hρ.1
  have := hσ.1
  exact (((hS.isAdmissible_iff_hasFixedBasis ρ).1 hρ).tprod
    ((hS.isAdmissible_iff_hasFixedBasis σ).1 hσ)).isAdmissible

/-- **`D_S(V) ⊗_{S^H} D_S(W) ≃ D_S(V ⊗_F W)` for admissible representations** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Exposé III, Proposition 1.5.2 p. 124 and §1.5.3 pp. 124–125): for a
regular ring `S` and admissible `V` and `W`, Fontaine's natural map `periodsTensor ρ σ act H` is
bijective. -/
theorem IsRegularPeriodRing.periodsTensor_bijective (hS : IsRegularPeriodRing act H)
    (hρ : ρ.IsAdmissible act H) (hσ : σ.IsAdmissible act H) :
    Function.Bijective (periodsTensor ρ σ act H) := by
  have := hρ.1
  have := hσ.1
  exact ((hS.isAdmissible_iff_hasFixedBasis ρ).1 hρ).periodsTensor_bijective
    ((hS.isAdmissible_iff_hasFixedBasis σ).1 hσ)

end Regular

end Representation
