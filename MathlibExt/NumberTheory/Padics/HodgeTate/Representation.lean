/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.Padics.HodgeTate

/-!
# Hodge–Tate representations

Let `K` be a subfield of `ℚ̄_p = PadicAlgCl p`, finite over `ℚ_p` for the main results, let
`G = Gal(ℚ̄_p / ℚ_p)` and `G_K = Gal(ℚ̄_p / K)`, and let `ρ` be a representation of `G` on a
`ℚ_p`-vector space `V`, restricted to `G_K`. Following J.-M. Fontaine and Y. Ouyang, *Theory of
p-adic Galois representations*, §6.1, and J.-M. Fontaine, *Représentations p-adiques
semi-stables*, Astérisque 223 (1994), Exposé III, §3.7 pp. 141–142, we define

* `Representation.IsHodgeTate`: `V` is **Hodge–Tate** over `K` if it is `B_HT`-admissible as a
  representation of `G_K` (Definition 6.3), for the Hodge–Tate ring `B_HT = ℂ_p[t, t⁻¹]` of
  `MathlibExt.NumberTheory.Padics.HodgeTate`: `V` is finite-dimensional and
  `D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}` has dimension `dim_{ℚ_p} V` over `B_HT^{G_K} = K`;
* `Representation.tateTwist`: the Tate twist `V(i) = V ⊗_{ℚ_p} ℚ_p(i)`, on which `σ` acts by
  `χ(σ)ⁱ ρ(σ)`, and `Representation.cyclotomic p`, the representation `ℚ_p(1)`;
* `Representation.twistPeriods`: the space `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`, a module over `ℂ_p^{G_K}`;
* `Representation.hodgeTateNumber`: the **Hodge–Tate numbers**, the natural-number dimension
  (`Module.finrank`, zero for infinite rank) of `(ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}` over `ℂ_p^{G_K}`; for
  `K` finite over `ℚ_p` and `V` finite-dimensional, this is
  `hᵢ = dim_K (ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}` (Definition 6.6).

## Main results

* `Representation.finrank_periods_hodgeTateAction_le`: `dim_K D_HT(V) ≤ dim_{ℚ_p} V`; and
  `Representation.isHodgeTate_iff_hasFixedBasis`,
  `Representation.isHodgeTate_iff_comparison_bijective`: the forms of admissibility agree, since
  `B_HT` is regular (Fontaine, *op. cit.*, Exposé III, Proposition 1.4.2 p. 123).
* `Representation.isHodgeTate_cyclotomic`, `Representation.hodgeTateNumber_cyclotomic`: `ℚ_p(1)` is
  Hodge–Tate, and for `K` finite over `ℚ_p`, `h₁ = 1` and `hᵢ = 0` for `i ≠ 1`, by Definition 6.6
  and Tate's theorems `ℂ_p^{G_K} = K` and `ℂ_p(j)^{G_K} = 0` for `j ≠ 0` (used in the proof of
  Proposition 6.2); Example 6.7 makes the same computation for the Tate module of an elliptic
  curve.

## Sign conventions

The numbers `hᵢ` are the Hodge–Tate numbers in the convention of Fontaine–Ouyang, for which
`ℚ_p(1)` has `h₁ = 1`. The literature on Galois representations attached to automorphic
representations uses the opposite sign: in T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor,
*Potential automorphy and change of weight*, Ann. of Math. 179 (2014), arXiv:1010.2561
(version 2), Notation, p. 8, for `K` finite over `ℚ_p`, a de Rham representation `W` of `G_K` on a
finite-dimensional `ℚ̄_p`-vector space and an embedding `τ : K → ℚ̄_p`, the multiset `HT_τ(W)` of
Hodge–Tate weights contains `i` with multiplicity `dim_{ℚ̄_p} (W ⊗_{τ, K} ℂ_p(i))^{G_K}`, so that
the cyclotomic character has `HT_τ(χ) = {-1}`. The Hodge–Tate weights are thus the negatives of the
indices `i` with `hᵢ ≠ 0`, counted with multiplicity and separated according to `τ`.

## Implementation notes

As in `MathlibExt.RepresentationTheory.AdmissibleRepresentation`, a representation of `G_K` is a
representation of `G` restricted to the subgroup `G_K`, no continuity is assumed, and the
finite-dimensionality of `V` is part of `Representation.IsAdmissible`. The `K`-vector spaces
`D_HT(V)` and `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` are modules over the rings of invariants `B_HT^{G_K}` and
`ℂ_p^{G_K}`, which are the images of `K` when `K` is finite over `ℚ_p`
(`PadicComplex.fixedSubalgebra_hodgeTateAction`, `PadicComplex.fixedSubalgebra_galoisAlgHom`);
dimensions are taken over these rings, as natural numbers (`Module.finrank`), and they are the
dimensions over `K` of Fontaine–Ouyang only for `K` finite over `ℚ_p` and `V` finite-dimensional.
-/

@[expose] public noncomputable section

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison
open scoped TensorProduct

namespace Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-! ### Tate twists -/

/-- **The Tate twist `V(i) = V ⊗_{ℚ_p} ℚ_p(i)`** of a representation `ρ` of `Gal(ℚ̄_p / ℚ_p)` on
`V`: the representation on `V` in which `σ` acts by `χ(σ)ⁱ ρ(σ)`, where
`χ(σ) = cyclotomicScalar p σ` is the `p`-adic cyclotomic character. -/
def tateTwist (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) :
    Representation ℚ_[p] (Galois p) V where
  toFun σ := cyclotomicScalar p σ ^ i • ρ σ
  map_one' := by rw [cyclotomicScalar_one, one_zpow, one_smul, map_one]
  map_mul' σ τ := by rw [cyclotomicScalar_mul, mul_zpow, map_mul, smul_mul_smul_comm]

/-- `σ` acts on `V(i)` by `χ(σ)ⁱ ρ(σ)`. -/
@[simp]
theorem tateTwist_apply (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) (σ : Galois p) :
    ρ.tateTwist i σ = cyclotomicScalar p σ ^ i • ρ σ :=
  rfl

/-- `V(0) = V`. -/
@[simp]
theorem tateTwist_zero (ρ : Representation ℚ_[p] (Galois p) V) : ρ.tateTwist 0 = ρ := by
  ext σ v
  simp

/-- `V(i)(j) = V(i + j)`. -/
theorem tateTwist_tateTwist (ρ : Representation ℚ_[p] (Galois p) V) (i j : ℤ) :
    (ρ.tateTwist i).tateTwist j = ρ.tateTwist (i + j) := by
  ext σ v
  simp [smul_smul, ← zpow_add₀ (cyclotomicScalar_ne_zero p σ), add_comm]

variable (p) in
/-- **The representation `ℚ_p(1)`**: the one-dimensional representation of `Gal(ℚ̄_p / ℚ_p)` on
`ℚ_p` in which `σ` acts by multiplication by the `p`-adic cyclotomic character
`χ(σ) = cyclotomicScalar p σ`, the Tate twist of the trivial representation by `1`. -/
def cyclotomic : Representation ℚ_[p] (Galois p) ℚ_[p] :=
  (trivial ℚ_[p] (Galois p) ℚ_[p]).tateTwist 1

/-- `σ` acts on `ℚ_p(1)` by multiplication by `χ(σ)`. -/
@[simp]
theorem cyclotomic_apply (σ : Galois p) (x : ℚ_[p]) :
    cyclotomic p σ x = cyclotomicScalar p σ * x := by
  simp [cyclotomic]

/-! ### Hodge–Tate representations -/

/-- **The `K`-vector space `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`**, for a representation `ρ` of
`Gal(ℚ̄_p / ℚ_p)` on `V`, `K` a subfield of `ℚ̄_p` and `G_K = Gal(ℚ̄_p / K)`: the elements of
`ℂ_p ⊗_{ℚ_p} V` fixed by the action `c ⊗ v ↦ χ(σ)ⁱ σ(c) ⊗ ρ(σ) v` of every `σ ∈ G_K`. It is
Fontaine's module `D_{ℂ_p}(V(i))` of the Tate twist `V(i)`, a module over the ring of invariants
`ℂ_p^{G_K}`, which is `K` when `K` is finite over `ℚ_p`
(`PadicComplex.fixedSubalgebra_galoisAlgHom`). -/
def twistPeriods (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (i : ℤ) :
    Submodule (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
      (ℂ_[p] ⊗[ℚ_[p]] V) :=
  (ρ.tateTwist i).periods (PadicComplex.galoisAlgHom p) K.fixingSubgroup

/-- `x ∈ (ℂ_p(i) ⊗ V)^{G_K}` if and only if `χ(σ)ⁱ (σ ⊗ ρ(σ)) x = x` for every `σ ∈ G_K`. -/
theorem mem_twistPeriods {ρ : Representation ℚ_[p] (Galois p) V}
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {i : ℤ} {x : ℂ_[p] ⊗[ℚ_[p]] V} :
    x ∈ ρ.twistPeriods K i ↔ ∀ σ ∈ K.fixingSubgroup,
      cyclotomicScalar p σ ^ i •
        TensorProduct.map (completionGalois p σ).toLinearMap (ρ σ) x = x := by
  simp only [twistPeriods, mem_periods, tateTwist_apply, TensorProduct.map_smul_right]
  rfl

/-- **The Hodge–Tate numbers** of a representation `ρ` of `Gal(ℚ̄_p / ℚ_p)` on `V` over a subfield
`K` of `ℚ̄_p`: `hᵢ` is the natural-number dimension (`Module.finrank`, zero for infinite rank)
of `(ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}` over the field of invariants `ℂ_p^{G_K}`. For `K` finite over
`ℚ_p`, `ℂ_p^{G_K} = K` (`PadicComplex.fixedSubalgebra_galoisAlgHom`), and for `V`
finite-dimensional this is `hᵢ = dim_K (ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}` (Fontaine–Ouyang,
Definition 6.6). With this convention `ℚ_p(1)` has `h₁ = 1`
(`Representation.hodgeTateNumber_cyclotomic`); its Hodge–Tate weight in the convention of the
literature on automorphic Galois representations is `-1`. -/
def hodgeTateNumber (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (i : ℤ) : ℕ :=
  Module.finrank (fixedSubalgebra ℂ_[p] (PadicComplex.galoisAlgHom p) K.fixingSubgroup)
    (ρ.twistPeriods K (-i))

/-- **`V` is Hodge–Tate over `K`** (Fontaine–Ouyang, Definition 6.3; Fontaine, Astérisque 223,
Exposé III, §3.7 p. 142), for a representation `ρ` of `Gal(ℚ̄_p / ℚ_p)` on `V` and a subfield `K`
of `ℚ̄_p`: `V` is `B_HT`-admissible as a representation of `G_K = Gal(ℚ̄_p / K)`, that is, `V` is
finite-dimensional and `dim_{B_HT^{G_K}} (B_HT ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, where
`B_HT = ℂ_p[t, t⁻¹]` carries the action `PadicComplex.hodgeTateAction p`; for `K` finite over
`ℚ_p`, `B_HT^{G_K} = K` (`PadicComplex.fixedSubalgebra_hodgeTateAction`). -/
def IsHodgeTate (ρ : Representation ℚ_[p] (Galois p) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ρ.IsAdmissible (PadicComplex.hodgeTateAction p) K.fixingSubgroup

section FiniteDimensional

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (ρ : Representation ℚ_[p] (Galois p) V)

/-- **`dim_K D_HT(V) ≤ dim_{ℚ_p} V`** (Fontaine, Astérisque 223, Exposé III, Proposition 1.4.2 (i)
p. 123, for the regular ring `B_HT`): for `K` finite over `ℚ_p` and a finite-dimensional `V`,
`D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}` has dimension at most `dim_{ℚ_p} V` over `B_HT^{G_K} = K`. -/
theorem finrank_periods_hodgeTateAction_le [FiniteDimensional ℚ_[p] V] :
    Module.finrank (fixedSubalgebra ℂ_[p][T;T⁻¹] (PadicComplex.hodgeTateAction p)
      K.fixingSubgroup) (ρ.periods (PadicComplex.hodgeTateAction p) K.fixingSubgroup) ≤
      Module.finrank ℚ_[p] V :=
  (PadicComplex.isRegularPeriodRing_hodgeTateAction p K).finrank_periods_le ρ

/-- **Hodge–Tate representations, basis form** (Fontaine, Astérisque 223, Exposé III,
Proposition 1.4.2 p. 123, for the regular ring `B_HT`): for `K` finite over `ℚ_p` and a
finite-dimensional `V`, `V` is Hodge–Tate over `K` if and only if `B_HT ⊗_{ℚ_p} V` has a
`B_HT`-basis of `G_K`-invariant vectors. -/
theorem isHodgeTate_iff_hasFixedBasis [FiniteDimensional ℚ_[p] V] :
    ρ.IsHodgeTate K ↔ ρ.HasFixedBasis (PadicComplex.hodgeTateAction p) K.fixingSubgroup :=
  (PadicComplex.isRegularPeriodRing_hodgeTateAction p K).isAdmissible_iff_hasFixedBasis ρ

/-- **Hodge–Tate representations, comparison form**: for `K` finite over `ℚ_p` and a
finite-dimensional `V`, `V` is Hodge–Tate over `K` if and only if the comparison map
`B_HT ⊗_K D_HT(V) → B_HT ⊗_{ℚ_p} V` is an isomorphism. -/
theorem isHodgeTate_iff_comparison_bijective [FiniteDimensional ℚ_[p] V] :
    ρ.IsHodgeTate K ↔
      Function.Bijective (ρ.comparison (PadicComplex.hodgeTateAction p) K.fixingSubgroup) :=
  (PadicComplex.isRegularPeriodRing_hodgeTateAction p K).isAdmissible_iff_comparison_bijective ρ

end FiniteDimensional

/-! ### The example of `ℚ_p(1)` -/

/-- The vector `t⁻¹ ⊗ 1` of `B_HT ⊗_{ℚ_p} ℚ_p(1)` is fixed by `Gal(ℚ̄_p / ℚ_p)`. -/
private theorem hodgeTateAction_T_neg_one_tmul (σ : Galois p) :
    TensorProduct.map (PadicComplex.hodgeTateAction p σ).toLinearMap (cyclotomic p σ)
      (T (-1) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])) = T (-1) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) := by
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, PadicComplex.hodgeTateAction_T,
    cyclotomic_apply, ← smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
    zpow_neg_one, mul_inv_cancel₀ (cyclotomicScalar_ne_zero p σ), one_smul]

/-- **`ℚ_p(1)` is Hodge–Tate** over every subfield `K` of `ℚ̄_p`: the `G_K`-invariant vector
`t⁻¹ ⊗ 1` is a `B_HT`-basis of `B_HT ⊗_{ℚ_p} ℚ_p(1)`. -/
theorem isHodgeTate_cyclotomic (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (cyclotomic p).IsHodgeTate K :=
  HasFixedBasis.isAdmissible ⟨1,
    (Algebra.TensorProduct.basis ℂ_[p][T;T⁻¹] (Module.Basis.singleton (Fin 1) ℚ_[p])).unitsSMul
      fun _ => (isUnit_T (-1)).unit, fun _ σ _ => by
    rw [Module.Basis.unitsSMul_apply, Algebra.TensorProduct.basis_apply,
      Module.Basis.singleton_apply, Units.smul_def, IsUnit.unit_spec, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
    exact hodgeTateAction_T_neg_one_tmul σ⟩

/-- Under `ℂ_p ⊗_{ℚ_p} ℚ_p ≅ ℂ_p`, the action `σ ⊗ χ(σ)` on `ℂ_p ⊗_{ℚ_p} ℚ_p(1)` becomes
`c ↦ χ(σ) σ(c)`. -/
private theorem rid_map_cyclotomic (σ : Galois p) (x : ℂ_[p] ⊗[ℚ_[p]] ℚ_[p]) :
    _root_.TensorProduct.rid ℚ_[p] ℂ_[p]
        (TensorProduct.map (completionGalois p σ).toLinearMap (cyclotomic p σ) x) =
      cyclotomicScalar p σ • completionGalois p σ (_root_.TensorProduct.rid ℚ_[p] ℂ_[p] x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c r =>
    rw [TensorProduct.map_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul, cyclotomic_apply,
      mul_smul, ← AlgEquiv.toLinearMap_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- `x ∈ (ℂ_p(j) ⊗_{ℚ_p} ℚ_p(1))^{G_K}` if and only if its image `c ∈ ℂ_p` satisfies
`χ(σ)^(j + 1) σ(c) = c` for every `σ ∈ G_K`. -/
private theorem mem_twistPeriods_cyclotomic_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (j : ℤ) (x : ℂ_[p] ⊗[ℚ_[p]] ℚ_[p]) :
    x ∈ (cyclotomic p).twistPeriods K j ↔ ∀ σ ∈ K.fixingSubgroup,
      cyclotomicScalar p σ ^ (j + 1) •
          completionGalois p σ (_root_.TensorProduct.rid ℚ_[p] ℂ_[p] x) =
        _root_.TensorProduct.rid ℚ_[p] ℂ_[p] x := by
  rw [mem_twistPeriods]
  refine forall₂_congr fun σ _ => ?_
  rw [← (_root_.TensorProduct.rid ℚ_[p] ℂ_[p]).injective.eq_iff, map_smul, rid_map_cyclotomic,
    smul_smul, ← zpow_add_one₀ (cyclotomicScalar_ne_zero p σ)]

/-- **The Hodge–Tate numbers of `ℚ_p(1)`** (from Fontaine–Ouyang, Definition 6.6): for `K` finite
over `ℚ_p` inside `ℚ̄_p`, `h₁ = 1` and `hᵢ = 0` for `i ≠ 1`, since
`(ℂ_p(-i) ⊗_{ℚ_p} ℚ_p(1))^{G_K} = ℂ_p(1 - i)^{G_K}` is `K` for `i = 1` and `0` otherwise, by
Tate's theorems `ℂ_p^{G_K} = K` and `ℂ_p(j)^{G_K} = 0` for `j ≠ 0`. -/
theorem hodgeTateNumber_cyclotomic (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (i : ℤ) :
    (cyclotomic p).hodgeTateNumber K i = if i = 1 then 1 else 0 := by
  rw [hodgeTateNumber]
  split_ifs with hi
  · subst hi
    let b := Algebra.TensorProduct.basis ℂ_[p] (Module.Basis.singleton (Fin 1) ℚ_[p])
    have hb (k : Fin 1) : b k ∈ (cyclotomic p).twistPeriods K (-1) := by
      rw [mem_twistPeriods_cyclotomic_iff]
      intro σ _
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.singleton_apply,
        TensorProduct.rid_tmul, one_smul, map_one, neg_add_cancel, zpow_zero, one_smul]
    exact (Module.finrank_eq_card_basis (periodsBasis b hb)).trans (Fintype.card_fin 1)
  · have hbot : (cyclotomic p).twistPeriods K (-i) = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h0 := (Set.ext_iff.1 (PadicComplex.fixedPoints_twist_eq_singleton_zero p K
        (show -i + 1 ≠ 0 by omega)) _).1 ((mem_twistPeriods_cyclotomic_iff K (-i) x).1 hx)
      exact (map_eq_zero_iff _ (_root_.TensorProduct.rid ℚ_[p] ℂ_[p]).injective).1 h0
    rw [hbot, finrank_bot]

end Representation
