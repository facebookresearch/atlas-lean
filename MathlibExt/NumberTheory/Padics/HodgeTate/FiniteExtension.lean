/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import MathlibExt.FieldTheory.Galois.FixingSubgroup
public import MathlibExt.NumberTheory.Padics.HodgeTate.Representation
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Descent

/-!
# Hodge–Tate representations over a finite extension

Let `K ⊆ L` be finite extensions of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`, with `G_L ≤ G_K` the
subgroups `Gal(ℚ̄_p/L) ≤ Gal(ℚ̄_p/K)` (`IntermediateField.fixingSubgroup`), and let `V` be a
representation of `Gal(ℚ̄_p/ℚ_p)`. We prove that `V` is Hodge–Tate over `K` if and only if it is
Hodge–Tate over `L` (`Representation.isHodgeTate_iff_of_le`), and that `V` has the same Hodge–Tate
numbers over `K` and over `L` (`Representation.hodgeTateNumber_eq_of_le`), for Hodge–Tate
representations and Hodge–Tate numbers as in J.-M. Fontaine and Y. Ouyang, *Theory of p-adic
Galois representations*, §6.1, Definitions 6.3 and 6.6.

When `L/K` is normal (that is, Galois), `G_L` is a normal subgroup of finite index of `G_K`, with
quotient `Gal(L/K)` (`MathlibExt.FieldTheory.Galois.FixingSubgroup`); the rings of invariants are
`B_HT^{G_K} = K` and `B_HT^{G_L} = L` (`PadicComplex.fixedSubalgebra_hodgeTateAction`), so that
`G_K/G_L` acts faithfully on the field `B_HT^{G_L}`, and similarly for `ℂ_p`
(`PadicComplex.fixedSubalgebra_galoisAlgHom`). Galois descent for admissibility
(`Representation.isAdmissible_iff_of_normal` and `Representation.finrank_periods_eq_of_normal`)
applies. For general `L`, we pass through the normal closure of `L` over `ℚ_p` inside `ℚ̄_p`,
which is normal over both `K` and `L`. This is J.-M. Fontaine, *Représentations p-adiques
semi-stables*, Astérisque 223 (1994), Exposé III, §1.8.6 p. 135, for the ring `B_HT`, whose
invariants are given in *op. cit.*, §3.5 p. 141.

As in `MathlibExt.NumberTheory.Padics.HodgeTate.Representation`, no continuity is assumed.
-/

@[expose] public section

open IntermediateField LaurentPolynomial MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- An element of `Gal(ℚ̄_p/ℚ_p)` fixing the image of `L` in `ℂ_p` lies in `G_L`. -/
private theorem mem_fixingSubgroup_of_forall_completionGalois_eq
    {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Galois p}
    (h : ∀ y : L, completionGalois p σ ((y : PadicAlgCl p) : ℂ_[p]) = (y : PadicAlgCl p)) :
    σ ∈ L.fixingSubgroup := by
  refine (mem_fixingSubgroup_iff L σ).2 fun y hy => ?_
  have := h ⟨y, hy⟩
  rw [PadicComplex.coe_eq, completionGalois_coe] at this
  exact (algebraMap (PadicAlgCl p) ℂ_[p]).injective this

/-- **Hodge–Tate over `K` and over a finite normal extension `L`**: for `K ≤ L` inside `ℚ̄_p` with
`L` finite over `ℚ_p` and `L/K` normal, `V` is Hodge–Tate over `K` if and only if it is
Hodge–Tate over `L`. -/
private theorem isHodgeTate_iff_of_normal {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (h : K ≤ L) [FiniteDimensional ℚ_[p] L] [Normal K (extendScalars h)]
    (ρ : Representation ℚ_[p] (Galois p) V) :
    ρ.IsHodgeTate K ↔ ρ.IsHodgeTate L := by
  have : FiniteDimensional K (extendScalars h) := finiteDimensional_extendScalars h
  have := finiteIndex_subgroupOf_fixingSubgroup h
  refine isAdmissible_iff_of_normal ρ (fixingSubgroup_le h)
    (normal_subgroupOf_fixingSubgroup h)
    (PadicComplex.isRegularPeriodRing_hodgeTateAction p L).isField fun σ _ hσ => ?_
  refine mem_fixingSubgroup_of_forall_completionGalois_eq fun y => ?_
  have := hσ _ (PadicComplex.hodgeTateFixedSubalgebraEquiv p L y).2
  rw [PadicComplex.coe_hodgeTateFixedSubalgebraEquiv, PadicComplex.hodgeTateAction_C] at this
  exact AddMonoidAlgebra.single_right_inj.mp this

/-- **The Hodge–Tate numbers over `K` and over a finite normal extension `L`**: for `K ≤ L`
inside `ℚ̄_p` with `L` finite over `ℚ_p` and `L/K` normal, `hᵢ` is the same over `K` and over
`L`. -/
private theorem hodgeTateNumber_eq_of_normal {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (h : K ≤ L) [FiniteDimensional ℚ_[p] L] [Normal K (extendScalars h)]
    (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) :
    ρ.hodgeTateNumber K i = ρ.hodgeTateNumber L i := by
  have : FiniteDimensional K (extendScalars h) := finiteDimensional_extendScalars h
  have := finiteIndex_subgroupOf_fixingSubgroup h
  refine finrank_periods_eq_of_normal (ρ.tateTwist (-i)) (fixingSubgroup_le h)
    (normal_subgroupOf_fixingSubgroup h)
    (isRegularPeriodRing_of_isField (Field.toIsField ℂ_[p]) (PadicComplex.galoisAlgHom p)
      L.fixingSubgroup).isField fun σ _ hσ => ?_
  refine mem_fixingSubgroup_of_forall_completionGalois_eq fun y => ?_
  have := hσ _ (PadicComplex.galoisFixedSubalgebraEquiv p L y).2
  rwa [PadicComplex.coe_galoisFixedSubalgebraEquiv, PadicComplex.galoisAlgHom_apply] at this

/-- **Hodge–Tate over `K` and over a finite extension `L`**: for `K ≤ L` inside `ℚ̄_p` with `L`
finite over `ℚ_p`, a representation `V` of `Gal(ℚ̄_p/ℚ_p)` is Hodge–Tate over `K` if and only
if it is Hodge–Tate over `L`. -/
theorem isHodgeTate_iff_of_le {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρ : Representation ℚ_[p] (Galois p) V) :
    ρ.IsHodgeTate K ↔ ρ.IsHodgeTate L := by
  have hLM := le_normalClosure L
  have := normal_extendScalars (h.trans hLM)
  have := normal_extendScalars hLM
  rw [isHodgeTate_iff_of_normal (h.trans hLM) ρ, isHodgeTate_iff_of_normal hLM ρ]

/-- **The Hodge–Tate numbers do not change under finite extension**: for `K ≤ L` inside `ℚ̄_p`
with `L` finite over `ℚ_p`, the Hodge–Tate numbers `hᵢ = dim (ℂ_p(-i) ⊗_{ℚ_p} V)^{G_K}` of a
representation `V` of `Gal(ℚ̄_p/ℚ_p)` over `K` are those over `L`. -/
theorem hodgeTateNumber_eq_of_le {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) :
    ρ.hodgeTateNumber K i = ρ.hodgeTateNumber L i := by
  have hLM := le_normalClosure L
  have := normal_extendScalars (h.trans hLM)
  have := normal_extendScalars hLM
  rw [hodgeTateNumber_eq_of_normal (h.trans hLM) ρ i, hodgeTateNumber_eq_of_normal hLM ρ i]

end Representation
