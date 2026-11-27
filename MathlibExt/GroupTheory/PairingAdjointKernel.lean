/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.lean`
and
`P2M/Sol/S_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.lean`
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

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Exponent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

open scoped Classical

private instance finiteMonoidHomUnits (G : Type*) [CommGroup G] [Finite G]
    (K : Type*) [Field K] : Finite (G →* Kˣ) := by
  classical
  haveI := Fintype.ofFinite G
  have hexp : 0 < Monoid.exponent G :=
    Monoid.exponent_pos.mpr Monoid.ExponentExists.of_finite
  let n : ℕ+ := ⟨Monoid.exponent G, hexp⟩
  let F : (G →* Kˣ) → (G → rootsOfUnity n K) := fun χ g =>
    ⟨χ g, by
      rw [mem_rootsOfUnity]
      show (χ g) ^ Monoid.exponent G = 1
      rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]⟩
  refine Finite.of_injective F fun χ χ' h => ?_
  ext g
  have := congrArg (fun f => ((f g : rootsOfUnity n K) : Kˣ)) h
  exact congrArg Units.val this

private theorem natCard_monoidHom_units_le (G : Type*) [CommGroup G] [Finite G]
    (K : Type*) [Field K] : Nat.card (G →* Kˣ) ≤ Nat.card G := by
  classical
  haveI := finiteMonoidHomUnits G K
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (G →* Kˣ)
  let ι : (G →* Kˣ) → (G →* K) := fun χ => (Units.coeHom K).comp χ
  have hι : Function.Injective ι := by
    intro χ χ' h
    ext g
    exact DFunLike.congr_fun h g
  have hli : LinearIndependent K
      (fun χ : G →* Kˣ => ((ι χ : G →* K) : G → K)) :=
    (linearIndependent_monoidHom G K).comp ι hι
  have h1 := LinearIndependent.fintype_card_le_finrank hli
  rw [Module.finrank_pi K, Fintype.card_eq_nat_card,
    Fintype.card_eq_nat_card] at h1
  exact h1

section Pairing

variable {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')

include hadd₁ in
private theorem e_zero_left (y : P) : e 0 y = 1 := by
  have h := hadd₁ 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

include hadd₂ in
private theorem e_zero_right (x : P) : e x 0 = 1 := by
  have h := hadd₂ x 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

include hadd₁ in
private theorem e_neg_left (x y : P) : e (-x) y = (e x y)⁻¹ := by
  have h := hadd₁ (-x) x y
  rw [neg_add_cancel, e_zero_left e hadd₁] at h
  exact eq_inv_of_mul_eq_one_left h.symm

include hadd₁ in
private theorem e_sub_left (x x' y : P) :
    e (x - x') y = e x y * (e x' y)⁻¹ := by
  rw [sub_eq_add_neg, hadd₁, e_neg_left e hadd₁]

include hadd₁ in
/-- The character of `Multiplicative P` attached to `y` by the pairing. -/
private def pairingChar (y : P) : Multiplicative P →* Kˣ where
  toFun x := e (Multiplicative.toAdd x) y
  map_one' := by
    show e 0 y = 1
    exact e_zero_left e hadd₁ y
  map_mul' a b := by
    show e (Multiplicative.toAdd a + Multiplicative.toAdd b) y = _
    exact hadd₁ _ _ _

include hadd₁ in
private theorem pairingChar_apply (y : P) (x : Multiplicative P) :
    pairingChar e hadd₁ y x = e (Multiplicative.toAdd x) y :=
  rfl

include hadd₂ in
/-- The right annihilator of a subgroup under the pairing. -/
private def pairingAnn (S : AddSubgroup P) : AddSubgroup P where
  carrier := {y | ∀ s ∈ S, e s y = 1}
  zero_mem' := fun s _ => e_zero_right e hadd₂ s
  add_mem' := by
    intro a b ha hb s hs
    show e s (a + b) = 1
    rw [hadd₂, ha s hs, hb s hs, one_mul]
  neg_mem' := by
    intro a ha s hs
    show e s (-a) = 1
    have h := hadd₂ s (-a) a
    rw [neg_add_cancel, e_zero_right e hadd₂, ha s hs, mul_one] at h
    exact h.symm

include hadd₂ in
private theorem mem_pairingAnn {S : AddSubgroup P} {y : P} :
    y ∈ pairingAnn e hadd₂ S ↔ ∀ s ∈ S, e s y = 1 :=
  Iff.rfl

include hadd₁ hadd₂ in
private theorem natCard_pairingAnn_mul_natCard
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y,
      ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (S : AddSubgroup P) :
    Nat.card (pairingAnn e hadd₂ S) * Nat.card S = Nat.card P := by
  classical
  haveI := finiteMonoidHomUnits (Multiplicative P) K
  haveI := finiteMonoidHomUnits (Multiplicative S) K
  let incl : Multiplicative S →* Multiplicative P :=
    AddMonoidHom.toMultiplicative S.subtype
  let ρ : (Multiplicative P →* Kˣ) →* (Multiplicative S →* Kˣ) :=
    { toFun := fun χ => χ.comp incl
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl }
  have hbij : Function.Bijective (pairingChar e hadd₁) := by
    constructor
    · intro y y' h
      have hy : ∀ x, e x (y - y') = 1 := by
        intro x
        have hx := DFunLike.congr_fun h (Multiplicative.ofAdd x)
        simp only [pairingChar_apply, toAdd_ofAdd] at hx
        have h2 := hadd₂ x (y - y') y'
        rw [sub_add_cancel, hx] at h2
        exact (mul_eq_right.mp h2.symm)
      exact sub_eq_zero.mp (hright _ hy)
    · intro χ
      obtain ⟨y, hy⟩ := hsurj χ
      exact ⟨y, MonoidHom.ext fun x => by rw [pairingChar_apply, hy]; rfl⟩
  have hcardHom : Nat.card (Multiplicative P →* Kˣ) = Nat.card P :=
    (Nat.card_eq_of_bijective _ hbij).symm
  have hker : Nat.card ρ.ker = Nat.card (pairingAnn e hadd₂ S) := by
    refine (Nat.card_eq_of_bijective
      (fun y : pairingAnn e hadd₂ S =>
        (⟨pairingChar e hadd₁ y.1, ?_⟩ : ρ.ker)) ⟨?_, ?_⟩).symm
    · rw [MonoidHom.mem_ker]
      refine MonoidHom.ext fun s => ?_
      show e (Multiplicative.toAdd (incl s)) y.1 = 1
      exact y.2 _ (by
        show ((S.subtype) (Multiplicative.toAdd s) : P) ∈ S
        exact (Multiplicative.toAdd s).2)
    · intro y y' h
      exact Subtype.ext (hbij.1
        (congrArg (fun z : ρ.ker => (z : Multiplicative P →* Kˣ)) h))
    · rintro ⟨χ, hχ⟩
      obtain ⟨y, rfl⟩ := hbij.2 χ
      refine ⟨⟨y, fun s hs => ?_⟩, rfl⟩
      have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hχ)
        (Multiplicative.ofAdd ⟨s, hs⟩)
      exact this
  have hle1 : Nat.card ρ.range ≤ Nat.card S :=
    (Nat.card_le_card_of_injective
      (fun χ : ρ.range => (χ : Multiplicative S →* Kˣ))
      Subtype.val_injective).trans
      (by
        have h := natCard_monoidHom_units_le (Multiplicative S) K
        rwa [Nat.card_congr Multiplicative.toAdd] at h)
  have hle2 : Nat.card S ≤ Nat.card ρ.range := by
    let ev : Multiplicative S → (ρ.range →* Kˣ) := fun s =>
      { toFun := fun χ => (χ : Multiplicative S →* Kˣ) s
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hev : Function.Injective ev := by
      intro s s' h
      have key : ∀ y : P,
          e (S.subtype (Multiplicative.toAdd s)) y =
            e (S.subtype (Multiplicative.toAdd s')) y := by
        intro y
        have := DFunLike.congr_fun h ⟨ρ (pairingChar e hadd₁ y), ⟨_, rfl⟩⟩
        exact this
      have hzero :
          (S.subtype (Multiplicative.toAdd s) : P) -
            S.subtype (Multiplicative.toAdd s') = 0 :=
        hleft _ fun y => by rw [e_sub_left e hadd₁, key y, mul_inv_cancel]
      have htoAdd : Multiplicative.toAdd s = Multiplicative.toAdd s' :=
        S.subtype_injective (sub_eq_zero.mp hzero)
      exact Multiplicative.toAdd.injective htoAdd
    calc Nat.card S = Nat.card (Multiplicative S) :=
          Nat.card_congr Multiplicative.toAdd.symm
      _ ≤ Nat.card (ρ.range →* Kˣ) :=
          Nat.card_le_card_of_injective ev hev
      _ ≤ Nat.card ρ.range := natCard_monoidHom_units_le _ K
  have hrange : Nat.card ρ.range = Nat.card S := le_antisymm hle1 hle2
  have hexact :
      Nat.card (Multiplicative P →* Kˣ) =
        Nat.card ρ.ker * Nat.card ρ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [← hcardHom, hexact, hker, hrange]

end Pairing

namespace AddMonoidHom

/-- Adjoint endomorphisms for a nondegenerate pairing on a finite abelian
group have kernels of the same cardinality. The pairing is assumed to
induce every character of the group, so the annihilator of the range of
one adjoint is the kernel of the other. -/
public theorem natCard_ker_eq_natCard_ker_of_pairing_adjoint
    {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y,
      ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card (T.ker) = Nat.card (T'.ker) := by
  classical
  have hkerT' : ∀ y, y ∈ T'.ker ↔ y ∈ pairingAnn e hadd₂ T.range := by
    intro y
    rw [AddMonoidHom.mem_ker, mem_pairingAnn]
    constructor
    · rintro h _ ⟨x, rfl⟩
      rw [hadj, h, e_zero_right e hadd₂]
    · intro h
      apply hright
      intro x
      rw [← hadj]
      exact h _ ⟨x, rfl⟩
  have hEq : T'.ker = pairingAnn e hadd₂ T.range := AddSubgroup.ext hkerT'
  have h1 := natCard_pairingAnn_mul_natCard e hadd₁ hadd₂ hleft hright hsurj
    T.range
  have h2 : Nat.card T.ker * Nat.card T.range = Nat.card P := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T.ker,
      mul_comm,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv]
  have hpos : 0 < Nat.card T.range := Nat.card_pos
  rw [hEq]
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

end AddMonoidHom
