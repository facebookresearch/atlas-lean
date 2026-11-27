/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ValuationSubring_ResidueValuationSubring.lean`,
`Theorems/Thm_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean`
and
`P2M/Sol/S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean`
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

public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {L : Type*} [Field L]

/-- The valuation subring of the residue field of `S` obtained as the image
of a smaller valuation subring `A ≤ S`. -/
noncomputable def residueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    ValuationSubring (ResidueField S) :=
  ValuationSubring.ofSubring ((residue S).comp (A.inclusion S h)).range <| by
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective x
    rcases A.mem_or_inv_mem (s : L) with hs | hs
    · exact Or.inl ⟨⟨s, hs⟩, rfl⟩
    · by_cases hu : IsUnit s
      · obtain ⟨u, rfl⟩ := hu
        have hinv : (((u⁻¹ : Sˣ) : S) : L) = ((u : S) : L)⁻¹ := map_units_inv S.subtype u
        refine Or.inr ⟨⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩, ?_⟩
        change residue S (A.inclusion S h ⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩) = (residue S u)⁻¹
        rw [← map_units_inv]
        rfl
      · refine Or.inl ⟨0, ?_⟩
        rw [map_zero, eq_comm, residue_eq_zero_iff]
        exact (_root_.mem_nonunits_iff.mpr hu)

/-- The natural map from `A` to its residue valuation subring in `S`. -/
noncomputable def toResidueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    A →+* A.residueValuationSubring S h :=
  ((residue S).comp (A.inclusion S h)).codRestrict (A.residueValuationSubring S h)
    fun a => ⟨a, rfl⟩

variable (A S : ValuationSubring L) (h : A ≤ S)

theorem mem_residueValuationSubring_iff {x : ResidueField S} :
    x ∈ A.residueValuationSubring S h ↔
      ∃ a : A, residue S (A.inclusion S h a) = x :=
  Iff.rfl

@[simp]
theorem coe_toResidueValuationSubring (a : A) :
    (A.toResidueValuationSubring S h a : ResidueField S) =
      residue S (A.inclusion S h a) :=
  rfl

theorem toResidueValuationSubring_surjective :
    Function.Surjective (A.toResidueValuationSubring S h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

theorem ker_toResidueValuationSubring :
    RingHom.ker (A.toResidueValuationSubring S h) = A.idealOfLE S h := by
  ext a
  rw [RingHom.mem_ker, ← Subtype.coe_inj, coe_toResidueValuationSubring,
    ZeroMemClass.coe_zero, residue_eq_zero_iff]
  rfl

end ValuationSubring

namespace ValuationSubring.ResidueKrullDim

open IsLocalRing

variable {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S)

private theorem length_le_height_add_coheight {α : Type*} [LinearOrder α]
    (a : α) (p : LTSeries α) :
    (p.length : ℕ∞) ≤ Order.height a + Order.coheight a := by
  classical
  set T : Finset (Fin (p.length + 1)) := Finset.univ.filter (fun i => p i ≤ a) with hT
  by_cases hTe : T.Nonempty
  · set i := T.max' hTe with hi
    have hiT : i ∈ T := T.max'_mem hTe
    have hia : p i ≤ a := (Finset.mem_filter.mp hiT).2
    have h1 : ((i : ℕ) : ℕ∞) ≤ Order.height a :=
      (Order.index_le_height p i).trans (Order.height_mono hia)
    by_cases hlast : (i : ℕ) = p.length
    · calc (p.length : ℕ∞) = ((i : ℕ) : ℕ∞) := by rw [hlast]
        _ ≤ Order.height a := h1
        _ ≤ Order.height a + Order.coheight a := le_self_add
    · have hilt : (i : ℕ) + 1 < p.length + 1 := by
        have := i.2
        omega
      set j : Fin (p.length + 1) := ⟨(i : ℕ) + 1, hilt⟩ with hj
      have hjT : j ∉ T := by
        intro hjT
        have := T.le_max' j hjT
        rw [← hi, Fin.le_def] at this
        simp [hj] at this
      have hja : a < p j := by
        by_contra hle
        push Not at hle
        exact hjT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
      have h2 : ((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1 ≤ Order.coheight a := by
        have hrev : (((j.rev : Fin (p.length + 1)) : ℕ) : ℕ∞) ≤ Order.coheight (p j) :=
          Order.rev_index_le_coheight p j
        have hrev' : ((j.rev : Fin (p.length + 1)) : ℕ) = p.length - ((i : ℕ) + 1) := by
          rw [Fin.val_rev]
          change p.length + 1 - ((i : ℕ) + 1 + 1) = p.length - ((i : ℕ) + 1)
          omega
        rw [hrev'] at hrev
        calc ((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1 ≤ Order.coheight (p j) + 1 := by
              gcongr
          _ ≤ Order.coheight a := Order.coheight_add_one_le hja
      calc (p.length : ℕ∞)
            = ((i : ℕ) : ℕ∞) + (((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1) := by
            norm_cast
            omega
        _ ≤ Order.height a + Order.coheight a := add_le_add h1 h2
  · have hall : ∀ i, a < p i := by
      intro i
      by_contra hle
      push Not at hle
      exact hTe ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩
    have h0 : ((((0 : Fin (p.length + 1)).rev : Fin (p.length + 1)) : ℕ) : ℕ∞) ≤
        Order.coheight (p 0) := Order.rev_index_le_coheight p 0
    rw [Fin.rev_zero, Fin.val_last] at h0
    calc (p.length : ℕ∞) ≤ Order.coheight (p 0) := h0
      _ ≤ Order.coheight (p 0) + 1 := le_self_add
      _ ≤ Order.coheight a := Order.coheight_add_one_le (hall 0)
      _ ≤ Order.height a + Order.coheight a := le_add_self

private theorem krullDim_eq_height_add_coheight {α : Type*} [LinearOrder α] (a : α) :
    Order.krullDim α = ((Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) := by
  haveI : Nonempty α := ⟨a⟩
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_length]
    exact WithBot.coe_mono (iSup_le fun p => length_le_height_add_coheight a p)
  · rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_mono (le_iSup (fun b => Order.height b + Order.coheight b) a)

private theorem krullDim_eq_krullDim_Iic_add_krullDim_Ici {α : Type*} [LinearOrder α]
    (a : α) :
    Order.krullDim α = Order.krullDim (Set.Iic a) + Order.krullDim (Set.Ici a) := by
  rw [krullDim_eq_height_add_coheight a, WithBot.coe_add, Order.height_eq_krullDim_Iic,
    Order.coheight_eq_krullDim_Ici]

private def subtypeIso {α β : Type*} [LE α] [LE β] (f : α ≃o β) {p : α → Prop}
    {q : β → Prop} (hpq : ∀ a, p a ↔ q (f a)) : {a // p a} ≃o {b // q b} where
  toEquiv := f.toEquiv.subtypeEquiv hpq
  map_rel_iff' {a b} := by
    change f a ≤ f b ↔ (a : α) ≤ b
    exact f.map_rel_iff

private abbrev overringsAbove (A : ValuationSubring L) := {T : ValuationSubring L // A ≤ T}

private def sigmaPt : overringsAbove A := ⟨S, h⟩

private noncomputable def isoIic :
    {P : (PrimeSpectrum A)ᵒᵈ // OrderDual.ofDual P ∈
        PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)} ≃o
      Set.Iic (sigmaPt A S h) :=
  subtypeIso (ValuationSubring.primeSpectrumOrderEquiv A) fun P => by
    change (A.idealOfLE S h : Set A) ⊆ (OrderDual.ofDual P).asIdeal ↔
      (⟨A.ofPrime (OrderDual.ofDual P).asIdeal, _⟩ : overringsAbove A) ≤ ⟨S, h⟩
    rw [SetLike.coe_subset_coe]
    constructor
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S
      conv_rhs => rw [← ValuationSubring.ofPrime_idealOfLE A S h]
      exact ValuationSubring.ofPrime_le_of_le A _ _ hle
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S at hle
      have := ValuationSubring.idealOfLE_le_of_le A _ _ (A.le_ofPrime _) h hle
      rwa [ValuationSubring.idealOfLE_ofPrime] at this

private noncomputable def isoIci : (PrimeSpectrum S)ᵒᵈ ≃o Set.Ici (sigmaPt A S h) :=
  (ValuationSubring.primeSpectrumOrderEquiv S).trans
    { toFun := fun T => ⟨⟨T.1, h.trans T.2⟩, T.2⟩
      invFun := fun T => ⟨T.1.1, T.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

private theorem krullDim_zeroLocus_eq :
    Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) =
      Order.krullDim (Set.Iic (sigmaPt A S h)) := by
  rw [← Order.krullDim_eq_of_orderIso (isoIic A S h), ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso
    { toEquiv := Equiv.refl _
      map_rel_iff' := Iff.rfl }

private theorem ringKrullDim_residue :
    ringKrullDim (A.residueValuationSubring S h) =
      Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) :=
  Order.krullDim_eq_of_orderIso
    (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (A.toResidueValuationSubring S h)
      (A.toResidueValuationSubring_surjective S h) (A.ker_toResidueValuationSubring S h))

private theorem ringKrullDim_eq_krullDim_Ici :
    ringKrullDim S = Order.krullDim (Set.Ici (sigmaPt A S h)) := by
  rw [ringKrullDim, ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso (isoIci A S h)

private theorem ringKrullDim_eq_krullDim_overrings :
    ringKrullDim A = Order.krullDim (overringsAbove A) := by
  rw [ringKrullDim, ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso (ValuationSubring.primeSpectrumOrderEquiv A)

end ValuationSubring.ResidueKrullDim

namespace ValuationSubring

/-- Krull dimension is additive for a valuation subring and the residue
valuation subring induced by a coarsening: for `A ≤ S` valuation subrings
of a field, `dim A = dim (residue of A in S) + dim S`. -/
theorem ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S := by
  rw [ResidueKrullDim.ringKrullDim_eq_krullDim_overrings,
    ResidueKrullDim.krullDim_eq_krullDim_Iic_add_krullDim_Ici (ResidueKrullDim.sigmaPt A S h),
    ResidueKrullDim.ringKrullDim_residue, ResidueKrullDim.krullDim_zeroLocus_eq,
    ResidueKrullDim.ringKrullDim_eq_krullDim_Ici A S h]

end ValuationSubring
