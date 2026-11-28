/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`ShannonBounds/BaseC21CosetData.lean` (shannon-capacity-lean,
https://github.com/spectra-research/shannon-capacity-lean, revision
aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65): the 26-point quotient code and the coset words
`(u, v, 2v + y, 2u + z)`, used here as `quotientCode` and `encode`.
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/

module

public import MathlibExt.Combinatorics.Coding.CycleCode
import Mathlib.Data.Finset.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# A code for the twenty-one-cycle in length 4096

The BPZ integer profiles define the requested cardinality. A code of size 11466 in
length four, obtained from 26 cosets, supplies a larger product code; taking a subset
realizes that cardinality in length 4096.

Source: Pjotr Buys, Sven Polak and Jeroen Zuiddam, *Lean-verified lower bounds for the
Shannon capacity of odd cycles*, arXiv:2607.29681v1 (2026), for the profiles; the 26-coset code
is from the authors' Lean repository https://github.com/spectra-research/shannon-capacity-lean,
revision aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65, `ShannonBounds/BaseC21CosetData.lean`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- **BPZ profiles.** A BPZ profile is an arbitrary quadruple of integers, called its code,
pairs, auxiliary and neutral coordinates: the four integer coordinates propagated by the
valid-tuple product of Buys, Polak and Zuiddam. No validity condition is imposed on the
quadruple.

Source: BPZ, arXiv:2607.29681, valid-tuple profiles. -/
structure BPZProfile where
  code : ℤ
  pairs : ℤ
  auxiliary : ℤ
  neutral : ℤ
  deriving DecidableEq, Repr

/-- **Product of BPZ profiles.** For $i = 1, 2$ let $p_i = (c_i, \pi_i, a_i, z_i)$ be a BPZ
profile, with integer code, pairs, auxiliary and neutral coordinates. The product $p_1 \star p_2$
is the BPZ profile with code coordinate $(c_1 - \pi_1)(c_2 - \pi_2) + a_1 \pi_2 + \pi_1 a_2$,
pairs coordinate $z_1 \pi_2 + \pi_1 z_2$, auxiliary coordinate $a_1 a_2$ and neutral coordinate
$z_1 z_2 + (a_1 - z_1)(a_2 - z_2)$.

The product is arithmetic on the four coordinates only; it does not supply an independent set.

Source: BPZ, arXiv:2607.29681, the profile product. -/
def BPZProfile.star (p₁ p₂ : BPZProfile) : BPZProfile where
  code :=
    (p₁.code - p₁.pairs) * (p₂.code - p₂.pairs) +
      p₁.auxiliary * p₂.pairs + p₁.pairs * p₂.auxiliary
  pairs := p₁.neutral * p₂.pairs + p₁.pairs * p₂.neutral
  auxiliary := p₁.auxiliary * p₂.auxiliary
  neutral :=
    p₁.neutral * p₂.neutral +
      (p₁.auxiliary - p₁.neutral) * (p₂.auxiliary - p₂.neutral)

/-- The four coordinates of the profile product in constructor form. -/
theorem BPZProfile.star_eq_mk (p₁ p₂ : BPZProfile) :
    p₁.star p₂ =
      ⟨(p₁.code - p₁.pairs) * (p₂.code - p₂.pairs) +
          p₁.auxiliary * p₂.pairs + p₁.pairs * p₂.auxiliary,
        p₁.neutral * p₂.pairs + p₁.pairs * p₂.neutral,
        p₁.auxiliary * p₂.auxiliary,
        p₁.neutral * p₂.neutral + (p₁.auxiliary - p₁.neutral) * (p₂.auxiliary - p₂.neutral)⟩ :=
  rfl

/-- **Iterated squaring of BPZ profiles.** Write $\star$ for the BPZ profile product. For a
natural number $k$ and a BPZ profile $p$, the $k$-fold iterated square $S_k(p)$ is defined by
$S_0(p) = p$ and $S_{k+1}(p) = S_k(p \star p)$; that is, $S_k(p)$ is obtained from $p$ by
squaring $k$ times under $\star$.

Source: BPZ, arXiv:2607.29681, iterated profile products. -/
def bpzProfileSquareIter : ℕ → BPZProfile → BPZProfile
  | 0, p => p
  | k + 1, p => bpzProfileSquareIter k (p.star p)

/-- **Buys–Polak–Zuiddam one-block profile for the 21-cycle.** This is the Buys–Polak–Zuiddam
(BPZ) profile whose code, pairs, auxiliary and neutral coordinates are $11441$, $10$,
$11441$ and $11398$.

Only these four integers are recorded, not BPZ's four-dimensional construction behind them.

Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction. -/
def bpzC21Pi1 : BPZProfile := ⟨11441, 10, 11441, 11398⟩
/-- **Buys–Polak–Zuiddam 1024-block profile for the 21-cycle.** Let $p_0$ be the one-block
21-cycle profile, whose code, pairs, auxiliary and neutral coordinates are $11441$, $10$,
$11441$ and $11398$, and let $p_{j+1} = p_j \star p_j$, where $\star$ is the
Buys–Polak–Zuiddam (BPZ) profile product. This profile is $p_{10}$, the result of squaring
$p_0$ ten times.

Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction. -/
def bpzC21Pi1024 : BPZProfile := bpzProfileSquareIter 10 bpzC21Pi1


private def quotientCode : Finset (ZMod 21 × ZMod 21) :=
  {(0, 2), (1, 19), (2, 15), (3, 6), (3, 10), (4, 2), (5, 19), (6, 15),
    (7, 7), (7, 11), (8, 3), (9, 20), (10, 16), (11, 8), (11, 12), (12, 4),
    (13, 0), (14, 17), (15, 13), (16, 5), (16, 9), (17, 1), (18, 18), (19, 14),
    (20, 6), (20, 10)}

private abbrev Near (x : ZMod 21) : Prop := x = -1 ∨ x = 0 ∨ x = 1

private abbrev WideNear (x : ZMod 21) : Prop :=
  x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3

private theorem wideNear_sub (x y : ZMod 21) (hx : Near x) (hy : Near y) :
    WideNear (x - 2 * y) := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide +kernel

private theorem quotient_separated :
    ∀ p ∈ quotientCode, ∀ q ∈ quotientCode,
      WideNear (p.1 - q.1) → WideNear (p.2 - q.2) → p = q := by
  decide +kernel

private theorem quotient_card : quotientCode.card = 26 := by
  decide +kernel

private def encode (p : (ZMod 21 × ZMod 21) × (ZMod 21 × ZMod 21)) :
    Fin 4 → ZMod 21 := ![p.2.1, p.2.2, 2 * p.2.2 + p.1.1, 2 * p.2.1 + p.1.2]

private theorem encode_injective : Function.Injective encode := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [encode, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h0 h1 h2 h3
  have hy : p.1.1 = q.1.1 := add_left_cancel (h1 ▸ h2)
  have hz : p.1.2 = q.1.2 := add_left_cancel (h0 ▸ h3)
  exact Prod.ext (Prod.ext hy hz) (Prod.ext h0 h1)

private def baseCode : Finset (Fin 4 → ZMod 21) :=
  (quotientCode ×ˢ (Finset.univ ×ˢ Finset.univ)).image encode

private theorem base_card : baseCode.card = 11466 := by
  rw [baseCode, Finset.card_image_of_injective _ encode_injective,
    Finset.card_product, Finset.card_product, quotient_card]
  decide +kernel

private theorem base_independent : IsCycleCode 21 baseCode := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ h
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hy : WideNear (p.1.1 - q.1.1) := by
    have ht := wideNear_sub _ _ (h 2) (h 1)
    convert ht using 1
    simp [encode]
    ring
  have hz : WideNear (p.1.2 - q.1.2) := by
    have ht := wideNear_sub _ _ (h 3) (h 0)
    convert ht using 1
    simp [encode]
    ring
  have hpq := quotient_separated p.1 (Finset.mem_product.mp hp).1
    q.1 (Finset.mem_product.mp hq).1 hy hz
  have hd : ∀ d : ZMod 21, Near d → Near (2 * d) → d = 0 := by decide +kernel
  have hu : p.2.1 = q.2.1 := by
    have h0 : Near (p.2.1 - q.2.1) := h 0
    have h3 : Near (2 * (p.2.1 - q.2.1)) := by
      convert (h 3 : Near ((encode p - encode q) 3)) using 1
      simp [encode, hpq]
      ring
    exact sub_eq_zero.mp (hd _ h0 h3)
  have hv : p.2.2 = q.2.2 := by
    have h1 : Near (p.2.2 - q.2.2) := h 1
    have h2 : Near (2 * (p.2.2 - q.2.2)) := by
      convert (h 2 : Near ((encode p - encode q) 2)) using 1
      simp [encode, hpq]
      ring
    exact sub_eq_zero.mp (hd _ h1 h2)
  have he : p = q := Prod.ext hpq (Prod.ext hu hv)
  simp [he]

private theorem target_le_product : bpzC21Pi1024.code.toNat ≤ 11466 ^ 1024 := by
  decide +kernel

private abbrev BaseWord := {w : Fin 4 → ZMod 21 // w ∈ baseCode}

private def flatten (f : Fin 1024 → BaseWord) (i : Fin 4096) : ZMod 21 :=
  let p := (finProdFinEquiv (m := 1024) (n := 4)).symm i
  (f p.1).1 p.2

private theorem flatten_injective : Function.Injective flatten := by
  intro f g h
  funext b
  apply Subtype.ext
  funext j
  simpa [flatten] using congrFun h (finProdFinEquiv (b, j))

private noncomputable instance productFintype : Fintype (Fin 1024 → BaseWord) :=
  Fintype.ofFinite _

open scoped Classical in
private noncomputable def productCode : Finset (Fin 4096 → ZMod 21) :=
  Finset.univ.image flatten

private theorem product_card : productCode.card = 11466 ^ 1024 := by
  classical
  calc
    productCode.card = Fintype.card (Fin 1024 → BaseWord) :=
      Finset.card_image_of_injective _ flatten_injective
    _ = Nat.card (Fin 1024 → BaseWord) := Fintype.card_eq_nat_card
    _ = Nat.card BaseWord ^ Nat.card (Fin 1024) := Nat.card_fun
    _ = baseCode.card ^ 1024 := by rw [Nat.card_eq_finsetCard, Nat.card_fin]
    _ = 11466 ^ 1024 := congrArg (fun n : ℕ => n ^ 1024) base_card

private theorem product_independent : IsCycleCode 21 productCode := by
  classical
  rintro _ ⟨a, ha, b, hb, rfl⟩ h
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hb
  have he : f = g := by
    funext b
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply base_independent _ ⟨(f b).1, (f b).2, (g b).1, (g b).2, rfl⟩
    intro j
    simpa [flatten] using h (finProdFinEquiv (b, j))
  simp [he]

/-- **Buys–Polak–Zuiddam code for the 21-cycle in length 4096.** Let $c$ be the code coordinate
of BPZ's final twenty-one-cycle profile after ten squarings, and let $M = \max(c, 0)$. There is
a finite set of words of length $4096$ over $\mathbb{Z}/21\mathbb{Z}$ that is an independent
code for the $21$-cycle and has exactly $M$ elements.

Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction in dimension 4096. -/
theorem bpz2026CycleTwentyOneConstruction :
  ∃ A : Finset (Fin 4096 → ZMod 21), IsCycleCode 21 A ∧ A.card = bpzC21Pi1024.code.toNat
    := by
  classical
  have hle : bpzC21Pi1024.code.toNat ≤ productCode.card := by
    rw [product_card]
    exact target_le_product
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq hle
  refine ⟨A, ?_, hcard⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩ h
  exact product_independent _ ⟨a, hA ha, b, hA hb, rfl⟩ h

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
