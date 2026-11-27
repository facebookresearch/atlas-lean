/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean`,
`ZInQKernel/Contrib/OneProof/AbstractPst.lean`, `ZInQKernel/Contrib/OneProof/AbstractPstGen.lean`,
`ZInQKernel/Contrib/OneProof/PanBergerPrinted.lean` and `ZInQKernel/Contrib/OneProof/PanBerger.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular
public import MathlibExt.RingTheory.Perfectoid.SemistablePeriodRingAbstract

/-!
# de Rham, crystalline, semistable and potentially semistable representations

Let `V` be a `ℚ_[p]`-linear representation of `G = Gal(ℚ̄_p/ℚ_p)` and let `K ⊆ ℚ̄_p` be an
extension of `ℚ_p`, with `G_K = Gal(ℚ̄_p/K)` (`IntermediateField.fixingSubgroup`). Following
J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
§5.1.2 p. 155 and §5.6.1 p. 166, with admissibility in the dimension form of Exposé III, §1.5.1
p. 124 (`Representation.IsAdmissible`), `V` is

* **de Rham over `K`** if it is `B_dR`-admissible as a representation of `G_K`
  (`Representation.IsDeRham`);
* **crystalline over `K`** if it is `B_cris`-admissible (`Representation.IsCrystalline`);
* **semistable over `K`** if it is `B_st`-admissible (`Representation.IsSemistable`);
* **potentially semistable** if it is semistable over some finite extension `K` of `ℚ_p` inside
  `ℚ̄_p` (`Representation.IsPotentiallySemistable`; Exposé III, §5.6.1 p. 166, in the form of
  §1.8.5 pp. 134–135).

Here `B_cris` and `B_st` are the Galois stable subrings `PadicComplexInt.bCris` and
`PadicComplexInt.bSt` of `B_dR`, as Fontaine identifies them (Exposé II, §4.1 pp. 83–84 and
§4.2.4–4.2.5 p. 86). By the equivariant isomorphisms with the abstract rings
`PadicComplexInt.BCris` and `PadicComplexInt.BSt = B_cris[X]` with `σ(X) = X + log [u_σ]`, the
same conditions over the abstract rings are equivalent (`Representation.isCrystalline_iff`,
`Representation.isSemistable_iff`, `Representation.isPotentiallySemistable_iff`), and since
`PadicComplexInt.bSt` does not depend on the choices of generators
(`PadicComplexInt.bSt_eq_adjoin_of_generators`), neither does potential semistability. The basis
form of admissibility over `B_st` implies potential semistability
(`Representation.isPotentiallySemistable_of_hasFixedBasis`).

The actions of `Gal(ℚ̄_p/ℚ_p)` on `B_dR`, `B_cris` and `B_st` are monoid homomorphisms
(`PadicComplexInt.galoisBDeRhamHom`, `PadicComplexInt.galoisBCrisHom`,
`PadicComplexInt.galoisBStHom`). As `B_dR` is a field, it is `(ℚ_p, G_K)`-regular
(`PadicComplexInt.isRegularPeriodRing_galoisBDeRhamHom`; Exposé III, Proposition 1.6.1 p. 125),
so the dimension, basis and comparison forms of `B_dR`-admissibility agree (Exposé III, §1.5): a
finite-dimensional `V` is de Rham over `K` if and only if `B_dR ⊗_{ℚ_p} V` has a `B_dR`-basis of
`G_K`-invariant vectors, if and only if the comparison map `α_V` is an isomorphism
(`Representation.isDeRham_iff_hasFixedBasis`, `Representation.isDeRham_iff_comparison_bijective`).
The regularity of `B_cris` and `B_st` is not proved here.

For a representation `ρ : G →* GL_n(ℚ̄_p)`, potential semistability means that `ρ` is defined over a
finite extension `E` of `ℚ_p` inside `ℚ̄_p` and the `ℚ_[p]`-representation `Eⁿ` is potentially
semistable (`PadicAlgCl.IsPotentiallySemistable`); likewise for de Rham
(`PadicAlgCl.IsDeRham`).

The predicates are defined for every `ℚ_[p]`-linear representation of `G`: the continuity of the
action, part of Fontaine's notion of a `p`-adic representation, is not assumed.
-/

@[expose] public noncomputable section

open Polynomial

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-- The action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on a Galois stable `ℚ_[p]`-subalgebra `B` of `B_dR`: the
restriction of `galoisBDeRham p σ`. -/
def galoisSubalgebra (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : Gal(PadicAlgCl p/ℚ_[p])), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : Gal(PadicAlgCl p/ℚ_[p])) : B →ₐ[ℚ_[p]] B :=
  ((galoisBDeRham p σ).comp B.val).codRestrict B fun x => hB σ x x.2

/-- `galoisSubalgebra p B hB σ` is the restriction of `galoisBDeRham p σ`. -/
@[simp]
theorem coe_galoisSubalgebra (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : Gal(PadicAlgCl p/ℚ_[p])), ∀ x ∈ B, galoisBDeRham p σ x ∈ B)
    (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : B) :
    (galoisSubalgebra p B hB σ x : 𝔹) = galoisBDeRham p σ x :=
  rfl

/-- The action of `Gal(ℚ̄_p/ℚ_p)` on `B_cris ⊆ B_dR`. -/
abbrev galoisBCris : Gal(PadicAlgCl p/ℚ_[p]) → bCris p →ₐ[ℚ_[p]] bCris p :=
  galoisSubalgebra p (bCris p) fun σ _ hx => galoisBDeRham_mem_bCris p σ hx

/-- The action of `Gal(ℚ̄_p/ℚ_p)` on `B_st ⊆ B_dR`. -/
abbrev galoisBSt : Gal(PadicAlgCl p/ℚ_[p]) → bSt p →ₐ[ℚ_[p]] bSt p :=
  galoisSubalgebra p (bSt p) fun σ _ hx => galoisBDeRham_mem_bSt p σ hx

/-- **The action of `Gal(ℚ̄_p/ℚ_p)` on `B_dR`, as a monoid homomorphism**, with coercion
`galoisBDeRham p` (`PadicComplexInt.galoisBDeRham_one`, `PadicComplexInt.galoisBDeRham_mul`). -/
def galoisBDeRhamHom : Gal(PadicAlgCl p/ℚ_[p]) →* (𝔹 →ₐ[ℚ_[p]] 𝔹) where
  toFun := galoisBDeRham p
  map_one' := galoisBDeRham_one p
  map_mul' := galoisBDeRham_mul p

/-- The coercion of `galoisBDeRhamHom p` is `galoisBDeRham p`. -/
@[simp]
theorem coe_galoisBDeRhamHom : ⇑(galoisBDeRhamHom p) = galoisBDeRham p :=
  rfl

/-- The action of `Gal(ℚ̄_p/ℚ_p)` on a Galois stable `ℚ_[p]`-subalgebra `B` of `B_dR`, as a monoid
homomorphism with coercion `galoisSubalgebra p B hB`. -/
def galoisSubalgebraHom (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : Gal(PadicAlgCl p/ℚ_[p])), ∀ x ∈ B, galoisBDeRham p σ x ∈ B) :
    Gal(PadicAlgCl p/ℚ_[p]) →* (B →ₐ[ℚ_[p]] B) where
  toFun := galoisSubalgebra p B hB
  map_one' := AlgHom.ext fun x => Subtype.ext (by simp)
  map_mul' σ τ := AlgHom.ext fun x => Subtype.ext (by simp [galoisBDeRham_mul])

/-- The coercion of `galoisSubalgebraHom p B hB` is `galoisSubalgebra p B hB`. -/
@[simp]
theorem coe_galoisSubalgebraHom (B : Subalgebra ℚ_[p] 𝔹)
    (hB : ∀ (σ : Gal(PadicAlgCl p/ℚ_[p])), ∀ x ∈ B, galoisBDeRham p σ x ∈ B) :
    ⇑(galoisSubalgebraHom p B hB) = galoisSubalgebra p B hB :=
  rfl

/-- **The action of `Gal(ℚ̄_p/ℚ_p)` on `B_cris ⊆ B_dR`, as a monoid homomorphism**, with coercion
`galoisBCris p`. -/
def galoisBCrisHom : Gal(PadicAlgCl p/ℚ_[p]) →* (bCris p →ₐ[ℚ_[p]] bCris p) :=
  galoisSubalgebraHom p (bCris p) fun σ _ hx => galoisBDeRham_mem_bCris p σ hx

/-- The coercion of `galoisBCrisHom p` is `galoisBCris p`. -/
@[simp]
theorem coe_galoisBCrisHom : ⇑(galoisBCrisHom p) = galoisBCris p :=
  rfl

/-- **The action of `Gal(ℚ̄_p/ℚ_p)` on `B_st ⊆ B_dR`, as a monoid homomorphism**, with coercion
`galoisBSt p`. -/
def galoisBStHom : Gal(PadicAlgCl p/ℚ_[p]) →* (bSt p →ₐ[ℚ_[p]] bSt p) :=
  galoisSubalgebraHom p (bSt p) fun σ _ hx => galoisBDeRham_mem_bSt p σ hx

/-- The coercion of `galoisBStHom p` is `galoisBSt p`. -/
@[simp]
theorem coe_galoisBStHom : ⇑(galoisBStHom p) = galoisBSt p :=
  rfl

/-- **`B_dR` is regular** (Fontaine, Exposé III, Proposition 1.6.1 p. 125): `B_dR` is a field
(`PadicComplexInt.instFieldBDeRham`), so it is `(ℚ_p, H)`-regular for every subgroup `H` of
`Gal(ℚ̄_p/ℚ_p)`, such as `G_K = Gal(ℚ̄_p/K)`. -/
theorem isRegularPeriodRing_galoisBDeRhamHom (H : Subgroup Gal(PadicAlgCl p/ℚ_[p])) :
    Representation.IsRegularPeriodRing (galoisBDeRhamHom p) H :=
  Representation.isRegularPeriodRing_of_isField (Field.toIsField 𝔹) _ H

end PadicComplexInt

namespace Representation

open PadicComplexInt

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- **`V` is de Rham over `K`** (Fontaine, Exposé III, §5.1.2 p. 155): `V` is `B_dR`-admissible as
a representation of `G_K = Gal(ℚ̄_p/K)`, that is,
`dim_{B_dR^{G_K}} (B_dR ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`. -/
def IsDeRham (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ρ.IsAdmissible (galoisBDeRham p) K.fixingSubgroup

/-- **`V` is crystalline over `K`** (Fontaine, Exposé III, §5.1.2 p. 155): `V` is
`B_cris`-admissible as a representation of `G_K = Gal(ℚ̄_p/K)`, that is,
`dim_{B_cris^{G_K}} (B_cris ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, for `B_cris ⊆ B_dR`. -/
def IsCrystalline (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ρ.IsAdmissible (galoisBCris p) K.fixingSubgroup

/-- **`V` is semistable over `K`** (Fontaine, Exposé III, §5.1.2 p. 155): `V` is
`B_st`-admissible as a representation of `G_K = Gal(ℚ̄_p/K)`, that is,
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, for `B_st = B_cris[log [p̃]] ⊆ B_dR`. -/
def IsSemistable (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ρ.IsAdmissible (galoisBSt p) K.fixingSubgroup

/-- **`V` is potentially semistable** (Fontaine, Exposé III, §5.6.1 p. 166, in the form of
§1.8.5 pp. 134–135): `V` is semistable over some finite extension `K` of `ℚ_p` inside `ℚ̄_p`. -/
def IsPotentiallySemistable (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ρ.IsSemistable K

/-- **Crystalline over the abstract `B_cris`**: `V` is crystalline over `K` if and only if it is
admissible for the abstract ring `B_cris = B_cris^+[1/t]` with its Galois action. -/
theorem isCrystalline_iff (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsCrystalline K ↔ ρ.IsAdmissible (BCris.galois p) K.fixingSubgroup :=
  (ρ.isAdmissible_iff_of_algEquiv (BCris.equivBCris p)
    (fun σ x => Subtype.ext (BCris.coe_equivBCris_galois p σ x)) K.fixingSubgroup).symm

/-- **Semistable over the abstract `B_st`**: `V` is semistable over `K` if and only if it is
admissible for the abstract ring `B_st = B_cris[X]`, with `σ(X) = X + log [u_σ]`. -/
theorem isSemistable_iff (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsSemistable K ↔ ρ.IsAdmissible (BSt.galois p) K.fixingSubgroup :=
  (ρ.isAdmissible_iff_of_algEquiv (BSt.equivBSt p)
    (fun σ x => Subtype.ext (BSt.coe_equivBSt_galois p σ x)) K.fixingSubgroup).symm

/-- **Potential semistability over the abstract `B_st`**: `V` is potentially semistable if and
only if, for some finite extension `K` of `ℚ_p` inside `ℚ̄_p`,
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` for the abstract ring `B_st = B_cris[X]`
with `σ(X) = X + log [u_σ]`. -/
theorem isPotentiallySemistable_iff (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) :
    ρ.IsPotentiallySemistable ↔ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K ∧ ρ.IsAdmissible (BSt.galois p) K.fixingSubgroup :=
  exists_congr fun K => and_congr_right fun _ => ρ.isSemistable_iff K

/-- **The basis form of potential semistability implies the dimension form**: if, for some finite
extension `K` of `ℚ_p` inside `ℚ̄_p`, `B_st ⊗_{ℚ_p} V` has a `B_st`-basis of `G_K`-invariant
vectors, then `V` is potentially semistable. -/
theorem isPotentiallySemistable_of_hasFixedBasis [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (h : ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K ∧ ρ.HasFixedBasis (galoisBSt p) K.fixingSubgroup) :
    ρ.IsPotentiallySemistable := by
  obtain ⟨K, hK, hb⟩ := h
  exact ⟨K, hK, hb.isAdmissible⟩

/-- **De Rham representations, basis form** (Fontaine, Exposé III, §1.5 and Proposition 1.6.1
p. 125): since `B_dR` is regular, a finite-dimensional `V` is de Rham over `K` if and only if
`B_dR ⊗_{ℚ_p} V` has a `B_dR`-basis of `G_K`-invariant vectors. -/
theorem isDeRham_iff_hasFixedBasis [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsDeRham K ↔ ρ.HasFixedBasis (galoisBDeRham p) K.fixingSubgroup :=
  (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup).isAdmissible_iff_hasFixedBasis ρ

/-- **De Rham representations, comparison form** (Fontaine, Exposé III, §1.5 and
Proposition 1.6.1 p. 125): since `B_dR` is regular, a finite-dimensional `V` is de Rham over `K`
if and only if the comparison map `α_V : B_dR ⊗_{B_dR^{G_K}} D_dR(V) → B_dR ⊗_{ℚ_p} V` is an
isomorphism, where `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}`. -/
theorem isDeRham_iff_comparison_bijective [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsDeRham K ↔ Function.Bijective (ρ.comparison (galoisBDeRham p) K.fixingSubgroup) :=
  IsRegularPeriodRing.isAdmissible_iff_comparison_bijective
    (isRegularPeriodRing_galoisBDeRhamHom p _) ρ

end Representation

namespace PadicAlgCl

variable {p : ℕ} [Fact p.Prime]

/-- **A representation `ρ : Gal(ℚ̄_p/ℚ_p) →* GL_n(ℚ̄_p)` is potentially semistable**: it takes
values in `GL_n(E)` for a finite extension `E` of `ℚ_p` inside `ℚ̄_p`, through a homomorphism
`ρ_E : Gal(ℚ̄_p/ℚ_p) →* GL_n(E)`, and the `ℚ_[p]`-representation `Eⁿ` given by `ρ_E` is
potentially semistable. -/
def IsPotentiallySemistable {n : ℕ} (ρ : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) (PadicAlgCl p)) :
    Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
      (Representation.ofGL ℚ_[p] ρE).IsPotentiallySemistable

/-- **A representation `ρ : Gal(ℚ̄_p/ℚ_p) →* GL_n(ℚ̄_p)` is de Rham**: it takes values in
`GL_n(E)` for a finite extension `E` of `ℚ_p` inside `ℚ̄_p`, through a homomorphism
`ρ_E : Gal(ℚ̄_p/ℚ_p) →* GL_n(E)`, and the `ℚ_[p]`-representation `Eⁿ` given by `ρ_E` is de Rham
over `ℚ_p`. -/
def IsDeRham {n : ℕ} (ρ : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
      (Representation.ofGL ℚ_[p] ρE).IsDeRham ⊥

end PadicAlgCl
