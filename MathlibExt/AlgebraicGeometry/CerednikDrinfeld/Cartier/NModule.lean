/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CartierNModule.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Int.Defs

/-!
# The module `N` attached to commuting operators

For commuting additive endomorphisms `V` and `Π` of an abelian group `M`,
`CerednikDrinfeld.CartierN.NMod V Π` is the quotient of `M × M` by the image of
`m ↦ (V m, -Π m)`. It carries the map `lambda` to `M` (`(m, m') ↦ Π m + V m'`), the map `toLie`
to `M ⧸ V.range`, the graded pieces `piece`, and, for a map `L : M →+ NMod V Π` compatible with
`V`, the endomorphism `phi`, its fixed subgroup `eta` and the map `u`.

`GradedCartierModuleData.NMod`, `lambda`, `phi`, `eta` and `u`
(`MathlibExt/RingTheory/WittVector/GradedCartierNModule.lean`) are given by the same formulas for
graded Cartier module data, where the quotient is a `WittVector p B`-module whose second factor
is the Frobenius twist `Sigma` of `M`. The construction here needs only the two maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

namespace CartierN

variable {M : Type u} [AddCommGroup M]

def beta (V Pi : M →+ M) : M →+ M × M :=
  V.prod (-Pi)

@[simp] theorem beta_apply (V Pi : M →+ M) (m : M) : beta V Pi m = (V m, -Pi m) := rfl

abbrev NMod (V Pi : M →+ M) : Type u :=
  (M × M) ⧸ (beta V Pi).range

def mk (V Pi : M →+ M) : M × M →+ NMod V Pi :=
  QuotientAddGroup.mk' (beta V Pi).range

abbrev cls (V Pi : M →+ M) (m m' : M) : NMod V Pi := mk V Pi (m, m')

theorem mk_apply (V Pi : M →+ M) (x : M × M) : mk V Pi x = (x : NMod V Pi) := rfl

theorem mk_surjective (V Pi : M →+ M) : Function.Surjective (mk V Pi) :=
  QuotientAddGroup.mk'_surjective _

theorem cls_surjective (V Pi : M →+ M) (z : NMod V Pi) : ∃ m m' : M, cls V Pi m m' = z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := mk_surjective V Pi z
  exact ⟨m, m', rfl⟩

theorem mk_eq_zero_iff (V Pi : M →+ M) (x : M × M) :
    mk V Pi x = 0 ↔ ∃ m : M, (V m, -Pi m) = x := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  rfl

theorem mk_eq_mk_iff (V Pi : M →+ M) (x y : M × M) :
    mk V Pi x = mk V Pi y ↔ ∃ m : M, y = x + (V m, -Pi m) := by
  rw [mk, QuotientAddGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨m, rfl⟩, h⟩
    exact ⟨m, h.symm⟩
  · rintro ⟨m, h⟩
    exact ⟨_, ⟨m, rfl⟩, h.symm⟩

@[simp] theorem cls_beta (V Pi : M →+ M) (m : M) : cls V Pi (V m) (-Pi m) = 0 :=
  (mk_eq_zero_iff V Pi _).2 ⟨m, rfl⟩

theorem cls_V_zero (V Pi : M →+ M) (m : M) : cls V Pi (V m) 0 = cls V Pi 0 (Pi m) := by
  have h : ((V m, 0) : M × M) = (0, Pi m) + (V m, -Pi m) := by ext <;> simp
  have h2 : cls V Pi (V m) 0 = cls V Pi 0 (Pi m) + cls V Pi (V m) (-Pi m) := by
    rw [cls, cls, cls, ← map_add, ← h]
  rw [h2, cls_beta, add_zero]

theorem cls_add_cls (V Pi : M →+ M) (m m' n n' : M) :
    cls V Pi m m' + cls V Pi n n' = cls V Pi (m + n) (m' + n') := by
  rw [cls, cls, cls, ← map_add]; rfl

def inl (V Pi : M →+ M) : M →+ NMod V Pi := (mk V Pi).comp (AddMonoidHom.inl M M)

def iota (V Pi : M →+ M) : M →+ NMod V Pi := (mk V Pi).comp (AddMonoidHom.inr M M)

@[simp] theorem inl_apply (V Pi : M →+ M) (m : M) : inl V Pi m = cls V Pi m 0 := rfl
@[simp] theorem iota_apply (V Pi : M →+ M) (m : M) : iota V Pi m = cls V Pi 0 m := rfl

theorem cls_eq_inl_add_iota (V Pi : M →+ M) (m m' : M) :
    cls V Pi m m' = inl V Pi m + iota V Pi m' := by
  rw [inl_apply, iota_apply, cls_add_cls, add_zero, zero_add]

theorem inl_comp_V (V Pi : M →+ M) : (inl V Pi).comp V = (iota V Pi).comp Pi := by
  ext m
  exact cls_V_zero V Pi m

theorem beta_range_le_ker_coprod (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (beta V Pi).range ≤ (Pi.coprod V).ker := by
  rintro _ ⟨m, rfl⟩
  have hm : Pi (V m) = V (Pi m) := DFunLike.congr_fun h m
  rw [AddMonoidHom.mem_ker, beta_apply, AddMonoidHom.coprod_apply, map_neg, hm, add_neg_cancel]

def lambda (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) : NMod V Pi →+ M :=
  QuotientAddGroup.lift (beta V Pi).range (Pi.coprod V) (beta_range_le_ker_coprod V Pi h)

@[simp] theorem lambda_cls (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) (m m' : M) :
    lambda V Pi h (cls V Pi m m') = Pi m + V m' := rfl

theorem lambda_mk (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) (x : M × M) :
    lambda V Pi h (mk V Pi x) = Pi x.1 + V x.2 := rfl

theorem lambda_comp_iota (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (lambda V Pi h).comp (iota V Pi) = V := by
  ext m
  change Pi 0 + V m = V m
  rw [map_zero, zero_add]

theorem lambda_comp_inl (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (lambda V Pi h).comp (inl V Pi) = Pi := by
  ext m
  change Pi m + V 0 = Pi m
  rw [map_zero, add_zero]

theorem beta_range_le_ker_toLie (V Pi : M →+ M) :
    (beta V Pi).range ≤ ((QuotientAddGroup.mk' V.range).comp (AddMonoidHom.fst M M)).ker := by
  rintro _ ⟨m, rfl⟩
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, beta_apply, AddMonoidHom.coe_fst,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨m, rfl⟩

def toLie (V Pi : M →+ M) : NMod V Pi →+ M ⧸ V.range :=
  QuotientAddGroup.lift (beta V Pi).range
      ((QuotientAddGroup.mk' V.range).comp (AddMonoidHom.fst M M))
    (beta_range_le_ker_toLie V Pi)

@[simp] theorem toLie_cls (V Pi : M →+ M) (m m' : M) :
    toLie V Pi (cls V Pi m m') = (m : M ⧸ V.range) := rfl

theorem toLie_surjective (V Pi : M →+ M) : Function.Surjective (toLie V Pi) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨cls V Pi m 0, rfl⟩

theorem toLie_comp_iota (V Pi : M →+ M) : (toLie V Pi).comp (iota V Pi) = 0 := by
  ext m
  rfl

section map

variable {M' : Type v} [AddCommGroup M']

theorem beta_range_le_ker_map₂ (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) :
    (beta V Pi).range ≤ ((mk V' Pi').comp (T₁.prodMap T₂)).ker := by
  rintro _ ⟨m, rfl⟩
  have h₁ : T₁ (V m) = V' (S m) := DFunLike.congr_fun hV m
  have h₂ : T₂ (Pi m) = Pi' (S m) := DFunLike.congr_fun hPi m
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, beta_apply]
  change cls V' Pi' (T₁ (V m)) (T₂ (-Pi m)) = 0
  rw [map_neg, h₁, h₂]
  exact cls_beta V' Pi' (S m)

def map₂ (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) : NMod V Pi →+ NMod V' Pi' :=
  QuotientAddGroup.lift (beta V Pi).range ((mk V' Pi').comp (T₁.prodMap T₂))
    (beta_range_le_ker_map₂ V Pi V' Pi' T₁ T₂ S hV hPi)

@[simp] theorem map₂_cls (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) (m m' : M) :
    map₂ V Pi V' Pi' T₁ T₂ S hV hPi (cls V Pi m m') = cls V' Pi' (T₁ m) (T₂ m') := rfl

def map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) : NMod V Pi →+ NMod V' Pi' :=
  map₂ V Pi V' Pi' T T T hV hPi

@[simp] theorem map_cls (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) (m m' : M) :
    map V Pi V' Pi' T hV hPi (cls V Pi m m') = cls V' Pi' (T m) (T m') := rfl

theorem lambda_comp_map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T)
    (h : Pi.comp V = V.comp Pi) (h' : Pi'.comp V' = V'.comp Pi') :
    (lambda V' Pi' h').comp (map V Pi V' Pi' T hV hPi) = T.comp (lambda V Pi h) := by
  ext ⟨m, m'⟩
  change Pi' (T m) + V' (T m') = T (Pi m + V m')
  rw [map_add, ← AddMonoidHom.comp_apply, ← hPi, ← AddMonoidHom.comp_apply V', ← hV]
  rfl

theorem toLie_comp_map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) :
    (toLie V' Pi').comp (map V Pi V' Pi' T hV hPi) =
      (QuotientAddGroup.map V.range V'.range T (by
        rintro _ ⟨m, rfl⟩
        exact ⟨T m, (DFunLike.congr_fun hV m).symm⟩)).comp (toLie V Pi) := by
  ext ⟨m, m'⟩
  rfl

end map

def piece (V Pi : M →+ M) (A A' : AddSubgroup M) : AddSubgroup (NMod V Pi) :=
  (A.prod A').map (mk V Pi)

theorem cls_mem_piece (V Pi : M →+ M) {A A' : AddSubgroup M} {m m' : M} (hm : m ∈ A)
    (hm' : m' ∈ A') : cls V Pi m m' ∈ piece V Pi A A' :=
  ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

theorem mem_piece_iff (V Pi : M →+ M) (A A' : AddSubgroup M) (z : NMod V Pi) :
    z ∈ piece V Pi A A' ↔ ∃ m ∈ A, ∃ m' ∈ A', cls V Pi m m' = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, ⟨hm, hm'⟩, rfl⟩
    exact ⟨m, hm, m', hm', rfl⟩
  · rintro ⟨m, hm, m', hm', rfl⟩
    exact cls_mem_piece V Pi hm hm'

theorem beta_range_le_ker_phi (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) :
    (beta V Pi).range ≤ (L.coprod (inl V Pi)).ker := by
  rintro _ ⟨m, rfl⟩
  have hm : L (V m) = inl V Pi (Pi m) := DFunLike.congr_fun hL m
  rw [AddMonoidHom.mem_ker, beta_apply, AddMonoidHom.coprod_apply, hm, map_neg, add_neg_cancel]

def phi (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    NMod V Pi →+ NMod V Pi :=
  QuotientAddGroup.lift (beta V Pi).range (L.coprod (inl V Pi)) (beta_range_le_ker_phi V Pi L hL)

@[simp] theorem phi_cls (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m m' : M) :
    phi V Pi L hL (cls V Pi m m') = L m + cls V Pi m' 0 := rfl

theorem phi_iota (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m : M) : phi V Pi L hL (iota V Pi m) = inl V Pi m := by
  rw [iota_apply, phi_cls, map_zero, zero_add, inl_apply]

theorem cls_zero_zero (V Pi : M →+ M) : cls V Pi 0 0 = 0 := map_zero (mk V Pi)

theorem phi_inl (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m : M) : phi V Pi L hL (inl V Pi m) = L m := by
  rw [inl_apply, phi_cls, cls_zero_zero, add_zero]

def eta (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    AddSubgroup (NMod V Pi) :=
  (phi V Pi L hL - AddMonoidHom.id (NMod V Pi)).ker

theorem mem_eta_iff (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (z : NMod V Pi) :
    z ∈ eta V Pi L hL ↔ phi V Pi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

def u (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    eta V Pi L hL →+ M ⧸ V.range :=
  (toLie V Pi).comp (eta V Pi L hL).subtype

@[simp] theorem u_apply (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (z : eta V Pi L hL) :
    u V Pi L hL z = toLie V Pi (z : NMod V Pi) := rfl

example : lambda (AddMonoidHom.id ℤ) (AddMonoidHom.id ℤ) rfl
    (cls (AddMonoidHom.id ℤ) (AddMonoidHom.id ℤ) 2 3) = 5 := rfl

example : cls (AddMonoidHom.id ℤ) (AddMonoidHom.id ℤ) 1 (-1) = 0 :=
  cls_beta (AddMonoidHom.id ℤ) (AddMonoidHom.id ℤ) 1

end CartierN

end CerednikDrinfeld

end
