/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.PotentiallySemistable

/-! Tests for de Rham, crystalline, semistable and potentially semistable representations: the
definitions unfold as stated, the conditions over the abstract rings `B_cris` and `B_st` agree
with the conditions over the subrings of `B_dR`, the basis form of admissibility over `B_st` (or
over the abstract `B_st`) implies potential semistability, the trivial representation is de Rham,
crystalline, semistable and potentially semistable, a matrix representation defined over a
finite extension `E` of `ℚ_p` is potentially semistable when `Eⁿ` is, the bundled Galois actions
have the expected coercions, and, as `B_dR` is regular, the comparison map for `B_dR` is
injective and the forms of being de Rham agree. -/

open PadicComplexInt Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

-- The definitions unfold as stated.
example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsDeRham K ↔ FiniteDimensional ℚ_[p] V ∧
      Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
        (ρ.periods (galoisBDeRham p) K.fixingSubgroup) = Module.finrank ℚ_[p] V :=
  Iff.rfl

example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) :
    ρ.IsPotentiallySemistable ↔ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K ∧ ρ.IsAdmissible (galoisBSt p) K.fixingSubgroup :=
  Iff.rfl

-- The action on `B_st ⊆ B_dR` is the restriction of the action on `B_dR`.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : bSt p) :
    (galoisBSt p σ x : 𝔹) = galoisBDeRham p σ x :=
  coe_galoisSubalgebra p _ _ σ x

-- Crystalline, semistable and potentially semistable over the abstract rings.
example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsCrystalline K ↔ ρ.IsAdmissible (BCris.galois p) K.fixingSubgroup :=
  ρ.isCrystalline_iff K

example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ρ.IsSemistable K ↔ ρ.IsAdmissible (BSt.galois p) K.fixingSubgroup :=
  ρ.isSemistable_iff K

example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (h : ρ.IsAdmissible (BSt.galois p) K.fixingSubgroup) : ρ.IsPotentiallySemistable :=
  ρ.isPotentiallySemistable_iff.2 ⟨K, inferInstance, h⟩

-- The basis form over `B_st`, or over the abstract `B_st = B_cris[X]`, implies potential
-- semistability.
example [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (h : ρ.HasFixedBasis (galoisBSt p) K.fixingSubgroup) : ρ.IsPotentiallySemistable :=
  ρ.isPotentiallySemistable_of_hasFixedBasis ⟨K, inferInstance, h⟩

example [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (h : ρ.HasFixedBasis (BSt.galois p) K.fixingSubgroup) : ρ.IsPotentiallySemistable :=
  ρ.isPotentiallySemistable_of_hasFixedBasis ⟨K, inferInstance,
    (ρ.hasFixedBasis_iff_of_algEquiv (BSt.equivBSt p)
      (fun σ x => Subtype.ext (BSt.coe_equivBSt_galois p σ x)) _).1 h⟩

-- The trivial representation is de Rham, crystalline and semistable over every `K`, and
-- potentially semistable: `1 ⊗ vᵢ` for a basis `(vᵢ)` of `V` is a basis of fixed vectors.
example [FiniteDimensional ℚ_[p] V] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (trivial ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V).IsDeRham K :=
  HasFixedBasis.isAdmissible ⟨_, Algebra.TensorProduct.basis 𝔹 (Module.finBasis ℚ_[p] V),
    fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

example [FiniteDimensional ℚ_[p] V] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (trivial ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V).IsCrystalline K :=
  HasFixedBasis.isAdmissible ⟨_, Algebra.TensorProduct.basis (bCris p)
    (Module.finBasis ℚ_[p] V), fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

example [FiniteDimensional ℚ_[p] V] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (trivial ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V).IsSemistable K :=
  HasFixedBasis.isAdmissible ⟨_, Algebra.TensorProduct.basis (bSt p)
    (Module.finBasis ℚ_[p] V), fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

example [FiniteDimensional ℚ_[p] V] :
    (trivial ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V).IsPotentiallySemistable :=
  isPotentiallySemistable_of_hasFixedBasis _ ⟨⊥, inferInstance, _,
    Algebra.TensorProduct.basis (bSt p) (Module.finBasis ℚ_[p] V), fun i σ _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

-- A matrix representation defined over a finite extension `E` of `ℚ_p` inside `ℚ̄_p` is
-- potentially semistable, resp. de Rham, when the `ℚ_[p]`-representation `Eⁿ` is.
example {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) E)
    (h : (ofGL ℚ_[p] ρE).IsPotentiallySemistable) :
    PadicAlgCl.IsPotentiallySemistable
      ((Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p))).comp ρE) :=
  ⟨E, inferInstance, ρE, fun _ => rfl, h⟩

example {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : Gal(PadicAlgCl p/ℚ_[p]) →* GL (Fin n) E) (h : (ofGL ℚ_[p] ρE).IsDeRham ⊥) :
    PadicAlgCl.IsDeRham ((Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p))).comp ρE) :=
  ⟨E, inferInstance, ρE, fun _ => rfl, h⟩

-- The bundled Galois actions on `B_dR` and `B_st ⊆ B_dR` have the expected coercions.
example (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : 𝔹) : galoisBDeRhamHom p σ x = galoisBDeRham p σ x :=
  rfl

example (σ τ : Gal(PadicAlgCl p/ℚ_[p])) (x : bSt p) :
    galoisBSt p (σ * τ) x = galoisBSt p σ (galoisBSt p τ x) := by
  rw [← coe_galoisBStHom, map_mul, AlgHom.mul_apply]

-- `B_dR` is regular: the comparison map is injective, `dim D_dR(V) ≤ dim V`, and a
-- finite-dimensional `V` whose comparison map is an isomorphism has a basis of invariant vectors.
example (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Injective (ρ.comparison (galoisBDeRham p) K.fixingSubgroup) :=
  (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup).comparison_injective ρ

example [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Module.finrank (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup)
      (ρ.periods (galoisBDeRham p) K.fixingSubgroup) ≤ Module.finrank ℚ_[p] V :=
  (isRegularPeriodRing_galoisBDeRhamHom p K.fixingSubgroup).finrank_periods_le ρ

example [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (h : Function.Bijective (ρ.comparison (galoisBDeRham p) K.fixingSubgroup)) :
    ρ.HasFixedBasis (galoisBDeRham p) K.fixingSubgroup :=
  (ρ.isDeRham_iff_hasFixedBasis K).1 ((ρ.isDeRham_iff_comparison_bijective K).2 h)
