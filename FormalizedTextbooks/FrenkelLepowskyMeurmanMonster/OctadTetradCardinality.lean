/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Compatible tetrad triples and canonical representatives modulo global complementation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadSignSpace
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
abbrev OctadTetradTriple := Fin 3 → Fin 4 → ZMod 2
abbrev OctadTetradParameters := ZMod 2 × (Fin 3 → Fin 3 → ZMod 2)

def octadTetradCompatible : Submodule (ZMod 2) OctadTetradTriple where
  carrier := {x | ∀ s : Fin 3, ∑ i, x s i = ∑ i, x 0 i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy s
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx s, hy s]
  smul_mem' := by
    intro c x hx s
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx s]

def octadTetradExtend (p : ZMod 2) (a : Fin 3 → ZMod 2) : Fin 4 → ZMod 2 :=
  Fin.snoc a (p + ∑ i, a i)

@[simp] theorem octadTetradExtend_free (p : ZMod 2) (a : Fin 3 → ZMod 2) (i : Fin 3) :
    octadTetradExtend p a i.castSucc = a i := Fin.snoc_castSucc _ _ _
@[simp] theorem octadTetradExtend_last (p : ZMod 2) (a : Fin 3 → ZMod 2) :
    octadTetradExtend p a (Fin.last 3) = p + ∑ i, a i := Fin.snoc_last _ _
@[simp] theorem octadTetradExtend_parity (p : ZMod 2) (a : Fin 3 → ZMod 2) :
    ∑ i, octadTetradExtend p a i = p := by
  rw [Fin.sum_univ_castSucc]
  simp only [octadTetradExtend_free, octadTetradExtend_last]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem octadTetradExtend_add (p q : ZMod 2) (a b : Fin 3 → ZMod 2) :
    octadTetradExtend (p+q) (a+b) = octadTetradExtend p a + octadTetradExtend q b := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Pi.add_apply, octadTetradExtend_last, Finset.sum_add_distrib]
    abel
  · simp only [Pi.add_apply, octadTetradExtend_free]

theorem octadTetradExtend_smul (c p : ZMod 2) (a : Fin 3 → ZMod 2) :
    octadTetradExtend (c*p) (c • a) = c • octadTetradExtend p a := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Pi.smul_apply, smul_eq_mul, octadTetradExtend_last, ← Finset.mul_sum]
    exact mul_add c p _ |>.symm
  · simp only [Pi.smul_apply, smul_eq_mul, octadTetradExtend_free]

def octadTetradEncode : OctadTetradParameters →ₗ[ZMod 2] octadTetradCompatible where
  toFun z := ⟨fun s => octadTetradExtend z.1 (z.2 s), by
    intro s
    simp only [octadTetradExtend_parity]⟩
  map_add' x y := by
    apply Subtype.ext
    funext s
    exact octadTetradExtend_add _ _ _ _
  map_smul' c x := by
    apply Subtype.ext
    funext s
    exact octadTetradExtend_smul _ _ _

@[simp] theorem octadTetradEncode_apply (z : OctadTetradParameters) (s : Fin 3) (i : Fin 4) :
    (octadTetradEncode z).val s i = octadTetradExtend z.1 (z.2 s) i := rfl

theorem octadTetradEncode_injective : Function.Injective octadTetradEncode := by
  intro x y h
  apply Prod.ext
  · have hp := congrArg (fun z : octadTetradCompatible => ∑ i, z.val 0 i) h
    simpa only [octadTetradEncode_apply, octadTetradExtend_parity] using hp
  · funext s i
    have hf := congrArg (fun z : octadTetradCompatible => z.val s i.castSucc) h
    simpa only [octadTetradEncode_apply, octadTetradExtend_free] using hf

theorem octadTetradEncode_surjective : Function.Surjective octadTetradEncode := by
  intro x
  refine ⟨(∑ i, x.val 0 i, fun s k => x.val s k.castSucc), ?_⟩
  apply Subtype.ext
  funext s i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [octadTetradEncode_apply, octadTetradExtend_last]
    have hp := x.property s
    rw [Fin.sum_univ_castSucc] at hp
    have he := congrArg (fun z : ZMod 2 => z + ∑ k : Fin 3, x.val s k.castSucc) hp
    calc
      _ = (∑ k : Fin 3, x.val s k.castSucc) + x.val s (Fin.last 3) +
          (∑ k : Fin 3, x.val s k.castSucc) := he.symm
      _ = ((∑ k : Fin 3, x.val s k.castSucc) +
          (∑ k : Fin 3, x.val s k.castSucc)) + x.val s (Fin.last 3) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
  · simp only [octadTetradEncode_apply, octadTetradExtend_free]

noncomputable def octadTetradEquiv : OctadTetradParameters ≃ₗ[ZMod 2] octadTetradCompatible :=
  LinearEquiv.ofBijective octadTetradEncode
    ⟨octadTetradEncode_injective, octadTetradEncode_surjective⟩

theorem octadTetradCompatible_card : Nat.card octadTetradCompatible = 1024 := by
  rw [← Nat.card_congr octadTetradEquiv.toEquiv]
  simp [OctadTetradParameters, Nat.card_eq_fintype_card, ZMod.card]

theorem octadTetradCompatible_finrank : Module.finrank (ZMod 2) octadTetradCompatible = 10 := by
  rw [← octadTetradEquiv.finrank_eq]
  simp [OctadTetradParameters, Module.finrank_prod, Module.finrank_pi_fintype]

/-- Simultaneously complement all three tetrads. -/
def octadTetradAllOne : octadTetradCompatible :=
  ⟨fun _ _ => 1, by intro s; rfl⟩
@[simp] theorem octadTetradAllOne_apply (s : Fin 3) (i : Fin 4) :
    octadTetradAllOne.val s i = 1 := rfl

def octadTetradAnchor : octadTetradCompatible →ₗ[ZMod 2] ZMod 2 where
  toFun x := x.val 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem octadTetradAnchor_apply (x : octadTetradCompatible) :
    octadTetradAnchor x = x.val 0 0 := rfl
@[simp] theorem octadTetradAnchor_one : octadTetradAnchor octadTetradAllOne = 1 := rfl

/-- The canonical representative has its first tetrad's first coordinate zero. -/
def octadTetradNormalized : Submodule (ZMod 2) octadTetradCompatible := octadTetradAnchor.ker
@[simp] theorem octadTetradNormalized_anchor (x : octadTetradNormalized) :
    octadTetradAnchor x.val = 0 := x.property

set_option backward.isDefEq.respectTransparency false in
/-- Add the first coordinate to every bit to normalize global complementation. -/
def octadTetradNormalize : octadTetradCompatible →ₗ[ZMod 2] octadTetradNormalized where
  toFun x := ⟨x + octadTetradAnchor x • octadTetradAllOne, by
    change octadTetradAnchor (x + octadTetradAnchor x • octadTetradAllOne) = 0
    rw [map_add, map_smul, octadTetradAnchor_one, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero _⟩
  map_add' x y := by
    apply Subtype.ext
    change (x+y) + octadTetradAnchor (x+y) • octadTetradAllOne =
      (x + octadTetradAnchor x • octadTetradAllOne) +
        (y + octadTetradAnchor y • octadTetradAllOne)
    rw [map_add, add_smul]
    abel
  map_smul' c x := by
    apply Subtype.ext
    change c • x + octadTetradAnchor (c • x) • octadTetradAllOne =
      c • (x + octadTetradAnchor x • octadTetradAllOne)
    rw [map_smul]
    change c • x + (c * octadTetradAnchor x) • octadTetradAllOne =
      c • (x + octadTetradAnchor x • octadTetradAllOne)
    rw [smul_add, smul_smul]

@[simp] theorem octadTetradNormalize_val (x : octadTetradCompatible) :
    (octadTetradNormalize x).val = x + octadTetradAnchor x • octadTetradAllOne := rfl

@[simp] theorem octadTetradNormalize_one : octadTetradNormalize octadTetradAllOne = 0 := by
  apply Subtype.ext
  change octadTetradAllOne + (1 : ZMod 2) • octadTetradAllOne = (0 : octadTetradCompatible)
  rw [one_smul]
  exact ZModModule.add_self octadTetradAllOne

@[simp] theorem octadTetradNormalize_normalized (x : octadTetradNormalized) :
    octadTetradNormalize x.val = x := by
  apply Subtype.ext
  rw [octadTetradNormalize_val, octadTetradNormalized_anchor, zero_smul, add_zero]

/-- A triple consists of its global complement bit and its unique normalized pattern. -/
def octadTetradDecompose : octadTetradCompatible →ₗ[ZMod 2]
    ZMod 2 × octadTetradNormalized := octadTetradAnchor.prod octadTetradNormalize

@[simp] theorem octadTetradDecompose_apply (x : octadTetradCompatible) :
    octadTetradDecompose x = (octadTetradAnchor x, octadTetradNormalize x) := rfl

theorem octadTetradDecompose_injective : Function.Injective octadTetradDecompose := by
  intro x y h
  have ha := congrArg Prod.fst h
  have hn := congrArg (fun z : ZMod 2 × octadTetradNormalized => z.2.val) h
  simp only [octadTetradDecompose_apply, octadTetradNormalize_val] at ha hn
  rw [ha] at hn
  exact add_right_cancel hn

theorem octadTetradDecompose_surjective : Function.Surjective octadTetradDecompose := by
  rintro ⟨c,x⟩
  refine ⟨x.val + c • octadTetradAllOne, ?_⟩
  rw [octadTetradDecompose_apply]
  apply Prod.ext
  · change octadTetradAnchor (x.val + c • octadTetradAllOne) = c
    rw [map_add, map_smul, octadTetradNormalized_anchor, octadTetradAnchor_one,
      zero_add, smul_eq_mul, mul_one]
  · change octadTetradNormalize (x.val + c • octadTetradAllOne) = x
    rw [map_add, map_smul, octadTetradNormalize_one, smul_zero, add_zero,
      octadTetradNormalize_normalized]

noncomputable def octadTetradComplementEquiv : octadTetradCompatible ≃ₗ[ZMod 2]
    ZMod 2 × octadTetradNormalized :=
  LinearEquiv.ofBijective octadTetradDecompose
    ⟨octadTetradDecompose_injective, octadTetradDecompose_surjective⟩

theorem octadTetradNormalized_card : Nat.card octadTetradNormalized = 512 := by
  have h := Nat.card_congr octadTetradComplementEquiv.toEquiv
  rw [octadTetradCompatible_card, Nat.card_prod, Nat.card_eq_fintype_card (α := ZMod 2),
    ZMod.card] at h
  omega

theorem octadTetradNormalized_finrank : Module.finrank (ZMod 2) octadTetradNormalized = 9 := by
  let : Module.Free (ZMod 2) octadTetradNormalized :=
    Module.Free.of_divisionRing (ZMod 2) octadTetradNormalized
  have h := octadTetradComplementEquiv.finrank_eq
  rw [octadTetradCompatible_finrank, Module.finrank_prod, Module.finrank_self] at h
  omega


@[simp] theorem octadTetradNormalize_apply (x : octadTetradCompatible) (s : Fin 3) (i : Fin 4) :
    (octadTetradNormalize x).val.val s i = x.val s i + x.val 0 0 := by
  rw [octadTetradNormalize_val]
  change x.val s i + x.val 0 0 * 1 = _
  exact congrArg (fun z : ZMod 2 => x.val s i + z) (mul_one _)

private theorem tetradBinaryScalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide +kernel

/-- Two equal-parity triples have the same canonical representative precisely
when they agree or differ by simultaneous complementation of all twelve bits. -/
theorem octadTetradNormalize_eq_iff (x y : octadTetradCompatible) :
    octadTetradNormalize x = octadTetradNormalize y ↔
      x = y ∨ x = y + octadTetradAllOne := by
  constructor
  · intro h
    have hn := congrArg Subtype.val h
    rw [octadTetradNormalize_val, octadTetradNormalize_val] at hn
    have he : x = y + (octadTetradAnchor y + octadTetradAnchor x) • octadTetradAllOne := by
      calc
        x = x + (octadTetradAnchor x + octadTetradAnchor x) • octadTetradAllOne := by
          rw [CharTwo.add_self_eq_zero, zero_smul, add_zero]
        _ = (x + octadTetradAnchor x • octadTetradAllOne) +
            octadTetradAnchor x • octadTetradAllOne := by rw [add_smul, add_assoc]
        _ = (y + octadTetradAnchor y • octadTetradAllOne) +
            octadTetradAnchor x • octadTetradAllOne :=
          congrArg (fun z => z + octadTetradAnchor x • octadTetradAllOne) hn
        _ = y + (octadTetradAnchor y + octadTetradAnchor x) • octadTetradAllOne := by
          rw [add_smul, add_assoc]
    rcases tetradBinaryScalar_cases (octadTetradAnchor y + octadTetradAnchor x) with hc | hc
    · rw [hc, zero_smul, add_zero] at he
      exact Or.inl he
    · rw [hc, one_smul] at he
      exact Or.inr he
  · rintro (rfl | h)
    · rfl
    · rw [h, map_add, octadTetradNormalize_one, add_zero]

theorem octadTetradNormalize_surjective : Function.Surjective octadTetradNormalize := by
  intro x
  exact ⟨x.val, octadTetradNormalize_normalized x⟩

def octadTetradComplementSpan : Submodule (ZMod 2) octadTetradCompatible :=
  Submodule.span (ZMod 2) {octadTetradAllOne}

theorem octadTetradAllOne_ne_zero : octadTetradAllOne ≠ 0 := by
  intro h
  have he := congrArg octadTetradAnchor h
  simp only [octadTetradAnchor_one, map_zero] at he
  exact one_ne_zero he

theorem octadTetradComplementSpan_card : Nat.card octadTetradComplementSpan = 2 := by
  have e := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) octadTetradCompatible
    octadTetradAllOne octadTetradAllOne_ne_zero
  change Nat.card (Submodule.span (ZMod 2) {octadTetradAllOne}) = 2
  rw [← Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The actual vector-space quotient by simultaneous complement has 512 elements. -/
theorem octadTetradComplementQuotient_card :
    Nat.card (octadTetradCompatible ⧸ octadTetradComplementSpan) = 512 := by
  have h := octadTetradComplementSpan.card_eq_card_quotient_mul_card
  rw [octadTetradCompatible_card, octadTetradComplementSpan_card] at h
  omega
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
