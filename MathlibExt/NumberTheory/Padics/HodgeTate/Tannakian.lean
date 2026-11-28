/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.Padics.HodgeTate.Representation
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Dual
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Exact
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Tensor

/-!
# Tannakian properties of Hodge–Tate representations

Let `K` be a finite extension of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`, let `G_K = Gal(ℚ̄_p / K)`,
and for a representation `ρ` of `Gal(ℚ̄_p / ℚ_p)` on a `ℚ_p`-vector space `V` let
`D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}` (`Representation.periods` for the action
`PadicComplex.hodgeTateAction p`), a vector space over `B_HT^{G_K} = K`. As `B_HT` is
`(ℚ_p, G_K)`-regular (`PadicComplex.isRegularPeriodRing_hodgeTateAction`), the results on
admissible representations for a regular ring of periods (J.-M. Fontaine and Y. Ouyang, *Theory
of p-adic Galois representations*, §3.1, Theorem 3.14 (2); J.-M. Fontaine, *Représentations
p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §1.5 pp. 124–125) give the following
for representations that are Hodge–Tate over `K` (`Representation.IsHodgeTate`).

* **Closure.** Subrepresentations and quotients of Hodge–Tate representations are Hodge–Tate
  (`Representation.IsHodgeTate.subrepresentation`, `Representation.IsHodgeTate.quotient`); more
  generally, so are the source of an injective intertwining map to a Hodge–Tate representation and
  the target of a surjective one from a Hodge–Tate representation
  (`Representation.IsHodgeTate.of_injective`, `Representation.IsHodgeTate.of_surjective`). A
  direct sum `V₁ × V₂` is Hodge–Tate if and only if `V₁` and `V₂` are
  (`Representation.isHodgeTate_prod_iff`, `Representation.IsHodgeTate.prod`), and tensor products
  and duals of Hodge–Tate representations are Hodge–Tate (`Representation.IsHodgeTate.tprod`,
  `Representation.IsHodgeTate.dual`).
* **Exactness and faithfulness.** On Hodge–Tate representations the functor `D_HT`
  (`Representation.periodsMap`) is exact (`Representation.IsHodgeTate.exact_periodsMap`,
  `Representation.IsHodgeTate.shortExact_periodsMap`) and faithful
  (`Representation.IsHodgeTate.eq_of_periodsMap_eq`).
* **Tensor products and duals.** For Hodge–Tate `V` and `W`, Fontaine's natural maps
  `D_HT(V) ⊗_K D_HT(W) → D_HT(V ⊗_{ℚ_p} W)` and `D_HT(V*) → D_HT(V)*` are isomorphisms
  (`Representation.IsHodgeTate.periodsTensorEquiv`,
  `Representation.IsHodgeTate.periodsDualEquiv`).

These are the statements of Fontaine–Ouyang, Theorem 3.14 (2), for `B = B_HT`: the Hodge–Tate
representations are stable under these operations, and `D_HT` is exact and faithful on them and
compatible with tensor products and duals. No category is constructed here. Here `V × W`,
`V ⊗_{ℚ_p} W` and `V*` are the representations `Representation.prod`, `Representation.tprod` and
`Representation.dual`; as in `MathlibExt.RepresentationTheory.AdmissibleRepresentation`, a
representation of `G_K` is a representation of `Gal(ℚ̄_p / ℚ_p)` restricted to `G_K`, and
continuity is never assumed.
-/

@[expose] public noncomputable section

open LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplex
open scoped TensorProduct

namespace Representation

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K] {V V₁ V₂ V₃ : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [AddCommGroup V₁] [Module ℚ_[p] V₁] [AddCommGroup V₂] [Module ℚ_[p] V₂] [AddCommGroup V₃]
  [Module ℚ_[p] V₃] {ρ : Representation ℚ_[p] (Galois p) V}
  {ρ₁ : Representation ℚ_[p] (Galois p) V₁} {ρ₂ : Representation ℚ_[p] (Galois p) V₂}
  {ρ₃ : Representation ℚ_[p] (Galois p) V₃}

/-- `V₁ → V₂ → V₂ ⧸ f(V₁)` is exact at `V₂`, for an intertwining map `f : V₁ → V₂`. -/
private theorem exact_mkQ_range (f : ρ₁.IntertwiningMap ρ₂) : Function.Exact f f.range.mkQ :=
  fun y => by
    rw [Subrepresentation.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl

/-- `ker g → V₂ → V₃` is exact at `V₂`, for an intertwining map `g : V₂ → V₃`. -/
private theorem exact_subtype_ker (g : ρ₂.IntertwiningMap ρ₃) : Function.Exact g.ker.subtype g :=
  fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩

/-! ### Closure properties -/

namespace IsHodgeTate

/-- **Subrepresentations of Hodge–Tate representations are Hodge–Tate** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over
`ℚ_p` inside `ℚ̄_p`, if `V` is Hodge–Tate over `K`, then so is every subrepresentation `W` of
`V`. -/
theorem subrepresentation (h : ρ.IsHodgeTate K) (W : Subrepresentation ρ) :
    W.toRepresentation.IsHodgeTate K :=
  (isRegularPeriodRing_hodgeTateAction p K).isAdmissible_toRepresentation h W

/-- **Quotients of Hodge–Tate representations are Hodge–Tate** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over
`ℚ_p` inside `ℚ̄_p`, if `V` is Hodge–Tate over `K`, then so is the quotient `V ⧸ W` of `V` by
every subrepresentation `W`. -/
theorem quotient (h : ρ.IsHodgeTate K) (W : Subrepresentation ρ) : W.quotient.IsHodgeTate K :=
  (isRegularPeriodRing_hodgeTateAction p K).isAdmissible_quotient h W

/-- **Hodge–Tate representations are closed under injective intertwining maps** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over
`ℚ_p` inside `ℚ̄_p`, if `V₂` is Hodge–Tate over `K` and `f : V₁ → V₂` is an injective
intertwining map, then `V₁` is Hodge–Tate over `K`. -/
theorem of_injective (h : ρ₂.IsHodgeTate K) {f : ρ₁.IntertwiningMap ρ₂}
    (hf : Function.Injective f) : ρ₁.IsHodgeTate K :=
  ((isRegularPeriodRing_hodgeTateAction p K).isAdmissible_of_exact hf f.range.mkQ_surjective
    (exact_mkQ_range f) h).1

/-- **Hodge–Tate representations are closed under surjective intertwining maps**
(Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for
`K` finite over `ℚ_p` inside `ℚ̄_p`, if `V₂` is Hodge–Tate over `K` and `g : V₂ → V₃` is a
surjective intertwining map, then `V₃` is Hodge–Tate over `K`. -/
theorem of_surjective (h : ρ₂.IsHodgeTate K) {g : ρ₂.IntertwiningMap ρ₃}
    (hg : Function.Surjective g) : ρ₃.IsHodgeTate K :=
  ((isRegularPeriodRing_hodgeTateAction p K).isAdmissible_of_exact g.ker.subtype_injective hg
    (exact_subtype_ker g) h).2

/-- **Tensor products of Hodge–Tate representations are Hodge–Tate** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over
`ℚ_p` inside `ℚ̄_p`, if `V₁` and `V₂` are Hodge–Tate over `K`, then so is `V₁ ⊗_{ℚ_p} V₂`, for the
tensor product representation `ρ₁.tprod ρ₂`. -/
theorem tprod (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K) : (ρ₁.tprod ρ₂).IsHodgeTate K :=
  (isRegularPeriodRing_hodgeTateAction p K).isAdmissible_tprod h₁ h₂

/-- **Duals of Hodge–Tate representations are Hodge–Tate** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over `ℚ_p` inside `ℚ̄_p`,
if `V` is Hodge–Tate over `K`, then so is its dual `V*`, for the dual representation
`ρ.dual`. -/
theorem dual (h : ρ.IsHodgeTate K) : ρ.dual.IsHodgeTate K :=
  (isRegularPeriodRing_hodgeTateAction p K).isAdmissible_dual h

end IsHodgeTate

/-- **Direct sums of Hodge–Tate representations** (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine,
Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over `ℚ_p` inside `ℚ̄_p`,
`V₁ × V₂` is Hodge–Tate over `K`, for the direct sum representation `ρ₁.prod ρ₂`, if and only if
`V₁` and `V₂` are Hodge–Tate over `K`. -/
theorem isHodgeTate_prod_iff :
    (ρ₁.prod ρ₂).IsHodgeTate K ↔ ρ₁.IsHodgeTate K ∧ ρ₂.IsHodgeTate K :=
  (isRegularPeriodRing_hodgeTateAction p K).isAdmissible_prod_iff

/-- **Direct sums of Hodge–Tate representations are Hodge–Tate**: for `K` finite over `ℚ_p`
inside `ℚ̄_p`, if `V₁` and `V₂` are Hodge–Tate over `K`, then so is `V₁ × V₂`, for the direct sum
representation `ρ₁.prod ρ₂`. -/
theorem IsHodgeTate.prod (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K) :
    (ρ₁.prod ρ₂).IsHodgeTate K :=
  isHodgeTate_prod_iff.2 ⟨h₁, h₂⟩

/-! ### The functor `D_HT` -/

namespace IsHodgeTate

/-- **`D_HT` is exact on Hodge–Tate representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over `ℚ_p` inside `ℚ̄_p`,
if `V₁ → V₂ → V₃` is an exact sequence of intertwining maps (the image of `f` is the kernel of
`g`) and `V₁` is Hodge–Tate over `K`, then `D_HT(V₁) → D_HT(V₂) → D_HT(V₃)` is exact. -/
theorem exact_periodsMap (h₁ : ρ₁.IsHodgeTate K) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hfg : Function.Exact f g) :
    Function.Exact (periodsMap (hodgeTateAction p) K.fixingSubgroup f)
      (periodsMap (hodgeTateAction p) K.fixingSubgroup g) :=
  (isRegularPeriodRing_hodgeTateAction p K).exact_periodsMap hfg h₁

/-- **`D_HT` maps short exact sequences of Hodge–Tate representations to short exact sequences**
(Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for
`K` finite over `ℚ_p` inside `ℚ̄_p` and a short exact sequence `0 → V₁ → V₂ → V₃ → 0` of
intertwining maps (`f` injective, `g` surjective, the image of `f` the kernel of `g`) with `V₂`
Hodge–Tate over `K`, the sequence `0 → D_HT(V₁) → D_HT(V₂) → D_HT(V₃) → 0` is exact. -/
theorem shortExact_periodsMap (h₂ : ρ₂.IsHodgeTate K) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Function.Injective (periodsMap (hodgeTateAction p) K.fixingSubgroup f) ∧
      Function.Exact (periodsMap (hodgeTateAction p) K.fixingSubgroup f)
        (periodsMap (hodgeTateAction p) K.fixingSubgroup g) ∧
      Function.Surjective (periodsMap (hodgeTateAction p) K.fixingSubgroup g) :=
  (isRegularPeriodRing_hodgeTateAction p K).shortExact_periodsMap hf hg hfg h₂

/-- **`D_HT` is faithful on Hodge–Tate representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over `ℚ_p` inside `ℚ̄_p`,
two intertwining maps `f, f' : V₁ → V₂` out of a representation `V₁` that is Hodge–Tate over `K`
with `D_HT(f) = D_HT(f')` are equal. -/
theorem eq_of_periodsMap_eq (h₁ : ρ₁.IsHodgeTate K) {f f' : ρ₁.IntertwiningMap ρ₂}
    (h : periodsMap (hodgeTateAction p) K.fixingSubgroup f =
      periodsMap (hodgeTateAction p) K.fixingSubgroup f') : f = f' :=
  (isRegularPeriodRing_hodgeTateAction p K).eq_of_periodsMap_eq h₁ h

/-- **`D_HT(V₁) ⊗_K D_HT(V₂) → D_HT(V₁ ⊗_{ℚ_p} V₂)` is bijective for Hodge–Tate
representations** (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5
pp. 124–125): for `K` finite over `ℚ_p` inside `ℚ̄_p` and `V₁`, `V₂` Hodge–Tate over `K`,
Fontaine's natural map `periodsTensor ρ₁ ρ₂ (hodgeTateAction p) K.fixingSubgroup`, from the tensor
product of `D_HT(V₁)` and `D_HT(V₂)` over `B_HT^{G_K} = K` to `D_HT(V₁ ⊗_{ℚ_p} V₂)`, is
bijective. -/
theorem periodsTensor_bijective (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K) :
    Function.Bijective (periodsTensor ρ₁ ρ₂ (hodgeTateAction p) K.fixingSubgroup) :=
  (isRegularPeriodRing_hodgeTateAction p K).periodsTensor_bijective h₁ h₂

/-- **The isomorphism `D_HT(V₁) ⊗_K D_HT(V₂) ≃ D_HT(V₁ ⊗_{ℚ_p} V₂)`** for `V₁` and `V₂`
Hodge–Tate over `K` finite over `ℚ_p` inside `ℚ̄_p`: Fontaine's natural map
`periodsTensor ρ₁ ρ₂ (hodgeTateAction p) K.fixingSubgroup`, as a linear equivalence over
`B_HT^{G_K} = K`. -/
def periodsTensorEquiv (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K) :
    ρ₁.periods (hodgeTateAction p) K.fixingSubgroup ⊗[fixedSubalgebra ℂ_[p][T;T⁻¹]
      (hodgeTateAction p) K.fixingSubgroup] ρ₂.periods (hodgeTateAction p) K.fixingSubgroup
        ≃ₗ[fixedSubalgebra ℂ_[p][T;T⁻¹] (hodgeTateAction p) K.fixingSubgroup]
      (ρ₁.tprod ρ₂).periods (hodgeTateAction p) K.fixingSubgroup :=
  LinearEquiv.ofBijective _ (h₁.periodsTensor_bijective h₂)

/-- The isomorphism `periodsTensorEquiv h₁ h₂` applied to `z` is Fontaine's natural map
`periodsTensor ρ₁ ρ₂ (hodgeTateAction p) K.fixingSubgroup` applied to `z`. -/
@[simp]
theorem periodsTensorEquiv_apply (h₁ : ρ₁.IsHodgeTate K) (h₂ : ρ₂.IsHodgeTate K)
    (z : ρ₁.periods (hodgeTateAction p) K.fixingSubgroup ⊗[fixedSubalgebra ℂ_[p][T;T⁻¹]
      (hodgeTateAction p) K.fixingSubgroup] ρ₂.periods (hodgeTateAction p) K.fixingSubgroup) :
    h₁.periodsTensorEquiv h₂ z = periodsTensor ρ₁ ρ₂ (hodgeTateAction p) K.fixingSubgroup z :=
  rfl

/-- **`D_HT(V*) → D_HT(V)*` is bijective for Hodge–Tate representations** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Astérisque 223, Exposé III, §1.5 pp. 124–125): for `K` finite over
`ℚ_p` inside `ℚ̄_p` and `V` Hodge–Tate over `K`, Fontaine's natural map
`ρ.periodsDual (hodgeTateAction p) K.fixingSubgroup`, from `D_HT(V*)` to the dual of `D_HT(V)`
over `B_HT^{G_K} = K`, is bijective. -/
theorem periodsDual_bijective (h : ρ.IsHodgeTate K) :
    Function.Bijective (ρ.periodsDual (hodgeTateAction p) K.fixingSubgroup) :=
  (isRegularPeriodRing_hodgeTateAction p K).periodsDual_bijective h

/-- **The isomorphism `D_HT(V*) ≃ D_HT(V)*`** for `V` Hodge–Tate over `K` finite over `ℚ_p`
inside `ℚ̄_p`: Fontaine's natural map `ρ.periodsDual (hodgeTateAction p) K.fixingSubgroup`, from
`D_HT(V*)` to the dual of `D_HT(V)` over `B_HT^{G_K} = K`, as a linear equivalence over
`B_HT^{G_K}`. -/
def periodsDualEquiv (h : ρ.IsHodgeTate K) :
    ρ.dual.periods (hodgeTateAction p) K.fixingSubgroup ≃ₗ[fixedSubalgebra ℂ_[p][T;T⁻¹]
      (hodgeTateAction p) K.fixingSubgroup] Module.Dual (fixedSubalgebra ℂ_[p][T;T⁻¹]
        (hodgeTateAction p) K.fixingSubgroup) (ρ.periods (hodgeTateAction p) K.fixingSubgroup) :=
  LinearEquiv.ofBijective _ h.periodsDual_bijective

/-- The isomorphism `periodsDualEquiv h` applied to `x` is Fontaine's natural map
`ρ.periodsDual (hodgeTateAction p) K.fixingSubgroup` applied to `x`. -/
@[simp]
theorem periodsDualEquiv_apply (h : ρ.IsHodgeTate K)
    (x : ρ.dual.periods (hodgeTateAction p) K.fixingSubgroup) :
    h.periodsDualEquiv x = ρ.periodsDual (hodgeTateAction p) K.fixingSubgroup x :=
  rfl

end IsHodgeTate

end Representation
