/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.lean`
and
`P2M/Sol/S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Henselian
public import MathlibExt.RingTheory.Valuation.InertiaSubgroupIn
import MathlibExt.RingTheory.Valuation.InertiaFixedField

/-!
# Henselian valuation rings of fields fixed by inertia

Let `A` be a valuation subring of an algebraically closed field `L`, and let `I` be a subgroup
of the `K`-algebra automorphisms of `L` contained in the inertia subgroup of `A`. We show that
the intersection of `A` with the subfield `L^I` of `L` fixed by `I` is a Henselian local ring.

The proof takes `L^I` itself as the base field: over `L^I`, the inertia subgroup of `A`
contains `I` and has fixed field exactly `L^I`, so the result follows from
`ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn`.
-/

@[expose] public section

universe u

open IsLocalRing Polynomial
open scoped Pointwise

noncomputable section

namespace HenselianFixedFieldAux

/-- Being a Henselian local ring transfers along ring isomorphisms. -/
private theorem henselianLocalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  let φ : S →+* R := e.symm
  have hmem : ∀ x : S, φ x ∈ maximalIdeal R ↔ x ∈ maximalIdeal S := fun x => by
    change e.symm x ∈ _ ↔ _
    rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      MulEquiv.isUnit_map]
  have hev : ∀ (g : S[X]) (x : S), (g.map φ).eval (φ x) = φ (g.eval x) := fun g x => by
    rw [eval_map, eval₂_hom]
  refine ⟨fun f hf a₀ h₀ hu => ?_⟩
  obtain ⟨a, ha, ha₀⟩ := HenselianLocalRing.is_henselian (f.map φ) (hf.map φ) (φ a₀)
    (by rw [hev, hmem]; exact h₀)
    (by rw [derivative_map, hev]; exact (MulEquiv.isUnit_map e.symm).mpr hu)
  have hφe : φ (e a) = a := e.symm_apply_apply a
  refine ⟨e a, ?_, ?_⟩
  · apply e.symm.injective
    change φ (f.eval (e a)) = φ 0
    rw [← hev, hφe, map_zero]
    exact ha
  · rw [← hmem, map_sub, hφe]
    exact ha₀

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable (I : Subgroup (L ≃ₐ[K] L))

/-- An element of `I` fixes `fixedField I` pointwise, so it is an automorphism over
`fixedField I`; if it lies in the inertia subgroup of `A` over `K`, it also lies in the inertia
subgroup of `A` over `fixedField I`. -/
private theorem fixingSubgroupEquiv_mem_inertiaSubgroupIn (hI : I ≤ A.inertiaSubgroupIn K)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ I) :
    IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField I)
        ⟨σ, (IntermediateField.le_fixedField_iff_le_fixingSubgroup I _).mp le_rfl hσ⟩ ∈
      A.inertiaSubgroupIn (IntermediateField.fixedField I) := by
  set F := IntermediateField.fixedField I
  set σ' := IntermediateField.fixingSubgroupEquiv F
    ⟨σ, (IntermediateField.le_fixedField_iff_le_fixingSubgroup I F).mp le_rfl hσ⟩
  have hσ' : ∀ x, σ' x = σ x := fun x => rfl
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.mp (hI hσ)
  have hστ : ∀ x, σ' x = (τ : L ≃ₐ[K] L) x := fun x => by rw [hσ', ← hτσ]; rfl
  have hdec : σ' ∈ A.decompositionSubgroup F := by
    rw [MulAction.mem_stabilizer_iff]
    have h := MulAction.mem_stabilizer_iff.mp τ.2
    refine SetLike.coe_injective ?_
    rw [ValuationSubring.coe_pointwise_smul]
    conv_rhs => rw [← h, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hστ]
  refine Subgroup.mem_map.mpr ⟨⟨σ', hdec⟩, ?_, rfl⟩
  have hτres : ∀ a : A, τ • residue A a = residue A a := fun a => by
    have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) τ = 1 :=
      MonoidHom.mem_ker.mp hτ
    have h2 := congrArg (fun e : RingAut (ResidueField A) => e (residue A a)) h1
    simpa [MulSemiringAction.toRingAut_apply] using h2
  refine MonoidHom.mem_ker.mpr (RingEquiv.ext fun r => ?_)
  obtain ⟨a, rfl⟩ := residue_surjective r
  have hsmul : (⟨σ', hdec⟩ : A.decompositionSubgroup F) • a = τ • a :=
    Subtype.ext (hστ (a : L))
  change (⟨σ', hdec⟩ : A.decompositionSubgroup F) • residue A a = residue A a
  rw [← ResidueField.residue_smul, hsmul, ResidueField.residue_smul, hτres]

/-- Over `fixedField I`, the inertia subgroup of `A` has fixed field `fixedField I`. -/
private theorem mem_fixedField_inertiaSubgroupIn_iff (hI : I ≤ A.inertiaSubgroupIn K) (x : L) :
    x ∈ IntermediateField.fixedField (A.inertiaSubgroupIn (IntermediateField.fixedField I)) ↔
      x ∈ IntermediateField.fixedField I := by
  refine ⟨fun hx => (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ =>
    (IntermediateField.mem_fixedField_iff _ _).mp hx _
      (fixingSubgroupEquiv_mem_inertiaSubgroupIn A I hI hσ), fun hx => ?_⟩
  exact (IntermediateField.mem_fixedField_iff _ _).mpr fun σ _ => σ.commutes ⟨x, hx⟩

/-- The valuation ring of `A` on the inertia fixed field over `fixedField I` is
`A ∩ fixedField I`. -/
private def ringEquiv (hI : I ≤ A.inertiaSubgroupIn K) :
    A.comap (algebraMap (IntermediateField.fixedField
        (A.inertiaSubgroupIn (IntermediateField.fixedField I))) L) ≃+*
      ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) where
  toFun b := ⟨((b : IntermediateField.fixedField
      (A.inertiaSubgroupIn (IntermediateField.fixedField I))) : L),
    Subring.mem_inf.mpr ⟨ValuationSubring.mem_comap.mp b.2,
      (mem_fixedField_inertiaSubgroupIn_iff A I hI _).mp (Subtype.prop _)⟩⟩
  invFun x := ⟨⟨x, (mem_fixedField_inertiaSubgroupIn_iff A I hI _).mpr
      (Subring.mem_inf.mp x.2).2⟩, ValuationSubring.mem_comap.mpr (Subring.mem_inf.mp x.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end HenselianFixedFieldAux

namespace ValuationSubring

/-- **Henselian valuation rings of inertia fixed fields.** Let `A` be a valuation subring of an
algebraically closed field `L`, where `L` is an algebra over a field `K`, and let `I` be a
subgroup of the group of `K`-algebra automorphisms of `L` contained in the inertia subgroup of
`A`: every element of `I` maps `A` onto itself and induces the identity on the residue field of
`A`. Then `A ∩ L^I` is a Henselian local ring, where `L^I` is the subfield of `L` fixed by
`I`. -/
public theorem henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  have := henselianLocalRing_comap_fixedField_inertiaSubgroupIn
    (K := IntermediateField.fixedField I) A
  HenselianFixedFieldAux.henselianLocalRing_of_ringEquiv (HenselianFixedFieldAux.ringEquiv A I hI)

end ValuationSubring

end
