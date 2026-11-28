/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Rat.Floor
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Equations over free groups and finite quotients (Kourovka Notebook Problem 14.48)

Kourovka Notebook, Archive of Solved Problems, Problem 14.48 (L. Comerford): if an equation over a
free group `F` has no solution in `F`, is there a finite quotient of `F` in which it has no
solution?

The theorem `unsolvableEquationUnsolvableInFiniteQuotient_refuted` gives a negative answer.
Its equation encodes three conditions with three extra free generators. Two of the conditions
force powers of distinct generators in the free group. The third asks for a product of conjugates
of those powers to be a cube. In a finite group the powers can be chosen to have 2-power order,
then conjugated into a common Sylow 2-subgroup, where cubing is bijective.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.48 (L.
Comerford). UnsolvedMath record UM-00701033 (`KOU-14.48`), dataset ulamai/UnsolvedMath v1.8.0.

An equation over `F` is an element `w` of `F ∗ F(x₀, …, xₙ₋₁)` (any number of unknowns); in the
quotient `F / N` its coefficients are mapped to `F / N`. Finite quotients are `F / N` with `N`
normal of finite index; `F` is free of any rank.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48Wanted

/-- **Kourovka Problem 14.48 (equations over free groups in finite quotients).** The statement
that for every free group $F$ on an arbitrary set of generators, every natural number $n$ and every
equation $w$ over $F$ in the unknowns $x_0, \dots, x_{n-1}$ (an element of the free product of $F$
with the free group on $x_0, \dots, x_{n-1}$): if no $g_0, \dots, g_{n-1} \in F$ are such that
substituting $g_i$ for $x_i$ sends $w$ to $1$, then there is a normal subgroup $N$ of finite index
in $F$ such that no $h_0, \dots, h_{n-1} \in F / N$ are such that substituting $h_i$ for $x_i$ and
mapping the coefficients of $w$ to their images in $F / N$ sends $w$ to $1$. -/
def unsolvableEquationUnsolvableInFiniteQuotient : Prop :=
  ∀ (α : Type) (n : ℕ) (w : Monoid.Coprod (FreeGroup α) (FreeGroup (Fin n))),
    (∀ x : Fin n → FreeGroup α, Monoid.Coprod.lift (MonoidHom.id _) (FreeGroup.lift x) w ≠ 1) →
    ∃ (N : Subgroup (FreeGroup α)) (_ : N.Normal), N.FiniteIndex ∧
      ∀ x : Fin n → FreeGroup α ⧸ N,
        Monoid.Coprod.lift (QuotientGroup.mk' N) (FreeGroup.lift x) w ≠ 1

open scoped commutatorElement

open Multiplicative (ofAdd toAdd)
open RegularWreathProduct

private abbrev Wreath := Multiplicative ℤ ≀ᵣ Multiplicative ℚ

-- A rational translation, with the integer coordinate counting crossings of integer boundaries.
private def countedShift : Multiplicative ℚ →* Wreath where
  toFun q := ⟨fun t ↦ ofAdd (⌊toAdd t⌋ - ⌊toAdd t - toAdd q⌋), q⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext t
      change ⌊toAdd t⌋ - ⌊toAdd t - 0⌋ = 0
      simp
    · rfl
  map_mul' q r := by
    apply RegularWreathProduct.ext
    · funext t
      change ⌊toAdd t⌋ - ⌊toAdd t - (toAdd q + toAdd r)⌋ =
        (⌊toAdd t⌋ - ⌊toAdd t - toAdd q⌋) +
          (⌊-toAdd q + toAdd t⌋ - ⌊-toAdd q + toAdd t - toAdd r⌋)
      rw [show -toAdd q + toAdd t = toAdd t - toAdd q by abel, sub_sub]
      abel
    · rfl

private abbrev shift : Multiplicative ℚ →* Wreath := RegularWreathProduct.inl

private theorem commute_unitShift (q : Multiplicative ℚ) :
    Commute (shift (ofAdd (-1))) (countedShift q) := by
  apply RegularWreathProduct.ext
  · funext t
    change 0 + (⌊-(-1 : ℚ) + toAdd t⌋ - ⌊-(-1 : ℚ) + toAdd t - toAdd q⌋) =
      (⌊toAdd t⌋ - ⌊toAdd t - toAdd q⌋) + 0
    rw [neg_neg, add_comm (1 : ℚ), add_sub_right_comm, Int.floor_add_one, Int.floor_add_one]
    omega
  · exact mul_comm _ _

-- If a and b are independent generators, no conjugate of a nonzero power of b
-- multiplied on the left by a nonzero power of a can be a cube.
private theorem no_cube {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (g z : FreeGroup Bool) :
    FreeGroup.of false ^ m * (g * FreeGroup.of true ^ n * g⁻¹) ≠ z ^ 3 := by
  -- The two powers shift the rational coordinate by +1 and -1. Only the first
  -- counts the crossing, so together they add 1 to every integer coordinate.
  let ρ : FreeGroup Bool →* Wreath := FreeGroup.lift fun b ↦
    if b then shift (ofAdd (-1 / (n : ℚ))) else countedShift (ofAdd (1 / (m : ℚ)))
  have hcomm (x : FreeGroup Bool) : Commute (shift (ofAdd (-1))) (ρ x) := by
    induction x with
    | one => simp
    | of b =>
      cases b
      · simpa [ρ] using commute_unitShift (ofAdd (1 / (m : ℚ)))
      · simpa [ρ] using (Commute.all (ofAdd (-1 : ℚ)) (ofAdd (-1 / (n : ℚ)))).map shift
    | inv_of _ ih => simpa using ih.inv_right
    | mul _ _ ih₁ ih₂ => simpa using ih₁.mul_right ih₂
  have pow_shift (d : ℤ) (hd : d ≠ 0) (v : ℚ) :
      (ofAdd (v / (d : ℚ))) ^ d = ofAdd v := by
    change d • (v / (d : ℚ)) = v
    rw [zsmul_eq_mul]
    field_simp
  have ha : ρ (FreeGroup.of false ^ m) = countedShift (ofAdd 1) := by
    rw [map_zpow]
    simp only [ρ, FreeGroup.lift_apply_of, Bool.false_eq_true, ite_false]
    rw [← map_zpow, pow_shift m hm]
  have hb : ρ (FreeGroup.of true ^ n) = shift (ofAdd (-1)) := by
    rw [map_zpow]
    simp only [ρ, FreeGroup.lift_apply_of, ite_true]
    rw [← map_zpow, pow_shift n hn]
  intro eqn
  have eq' := congrArg ρ eqn
  rw [map_mul, map_mul, map_mul, ha, hb, map_inv, ← (hcomm g).eq, mul_assoc,
    mul_inv_cancel, mul_one, map_pow] at eq'
  -- Any cube root would have zero rational shift. Its cube therefore acts at
  -- each point by adding three times an integer, which cannot give 1.
  have hr := congrArg (fun w : Wreath ↦ toAdd w.right) eq'
  change 1 + (-1 : ℚ) = _ at hr
  simp only [pow_succ, pow_zero, one_mul, mul_right, toAdd_mul] at hr
  have hz : (ρ z).right = 1 := show toAdd (ρ z).right = 0 by linarith
  have hl := congrArg (fun w : Wreath ↦ toAdd (w.left 1)) eq'
  simp only [pow_succ, pow_zero, one_mul, mul_left, mul_right, hz, mul_one, inv_one,
    Pi.mul_apply, toAdd_mul] at hl
  change (⌊(0 : ℚ)⌋ - ⌊0 - (1 : ℚ)⌋) + 0 = _ at hl
  norm_num at hl
  omega

-- The first two relators constrain the unknowns u and v to centralize a and b.
-- The last asks for a cube which is a product of conjugates of a*u² and b*v².
private def relators {G : Type*} [Group G] (a b : G) (x : Fin 4 → G) : Fin 3 → G :=
  ![⁅a, x 0⁆, ⁅b, x 1⁆,
    (a * x 0 ^ 2 * (x 2 * (b * x 1 ^ 2) * (x 2)⁻¹)) / x 3 ^ 3]

private theorem map_relators {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (x : Fin 4 → G) (i : Fin 3) :
    f (relators a b x i) = relators (f a) (f b) (f ∘ x) i := by
  fin_cases i <;> simp [relators, map_commutatorElement]

private theorem no_free_solution (x : Fin 4 → FreeGroup Bool)
    (sol : ∀ i, relators (FreeGroup.of false) (FreeGroup.of true) x i = 1) : False := by
  obtain ⟨u, hu⟩ := FreeGroup.commute_of_iff.mp (commutatorElement_eq_one_iff_commute.mp (sol 0))
  obtain ⟨v, hv⟩ := FreeGroup.commute_of_iff.mp (commutatorElement_eq_one_iff_commute.mp (sol 1))
  have hx := div_eq_one.mp (sol 2)
  change FreeGroup.of false * x 0 ^ 2 * (x 2 * (FreeGroup.of true * x 1 ^ 2) * (x 2)⁻¹) =
    x 3 ^ 3 at hx
  have oddpow (b : Bool) (k : ℤ) :
      FreeGroup.of b * (FreeGroup.of b ^ k) ^ 2 = FreeGroup.of b ^ (1 + k * 2) := by
    rw [zpow_add, zpow_mul, zpow_one, zpow_ofNat]
  rw [← hu, ← hv, oddpow, oddpow] at hx
  exact no_cube (by omega) (by omega) _ _ hx

private theorem finite_solution {G : Type*} [Group G] [Finite G] (a b : G) :
    ∃ x : Fin 4 → G, ∀ i, relators a b x i = 1 := by
  obtain ⟨k, m, ⟨j, hj⟩, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  -- Raising both coefficients to the odd part of the group order gives 2-elements.
  have syl (c : G) : ∃ P : Sylow 2 G, c ^ m ∈ P := by
    have hp : IsPGroup 2 (Subgroup.zpowers (c ^ m)) := by
      rintro ⟨_, i, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      change ((c ^ m) ^ i) ^ (2 ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, ← pow_mul,
        mul_comm m, ← hcard, pow_card_eq_one', one_zpow]
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers _)⟩
  obtain ⟨P, ha⟩ := syl a
  obtain ⟨Q, hb⟩ := syl b
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hb' : g * b ^ m * g⁻¹ ∈ P := by
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hb
  let t : P := ⟨a ^ m * (g * b ^ m * g⁻¹), P.mul_mem ha hb'⟩
  obtain ⟨z, hz⟩ := (P.isPGroup.powEquiv (n := 3) (by decide)).surjective t
  have hc : (z : G) ^ 3 = (t : G) := congrArg Subtype.val hz
  have hm (c : G) : c * (c ^ j) ^ 2 = c ^ m := by
    rw [hj, ← pow_mul, mul_comm j, pow_succ']
  refine ⟨![a ^ j, b ^ j, g, (z : G)], ?_⟩
  intro i
  fin_cases i
  · exact (Commute.self_pow a j).commutator_eq
  · exact (Commute.self_pow b j).commutator_eq
  · apply div_eq_one.mpr
    change a * (a ^ j) ^ 2 * (g * (b * (b ^ j) ^ 2) * g⁻¹) = (z : G) ^ 3
    rw [hm, hm]
    exact hc.symm

private abbrev Alphabet := Bool ⊕ Fin 3
private abbrev F := FreeGroup Alphabet

-- Three extra free generators let one equation record all three relators.
private def markedProduct {G : Type*} [Group G] (r t : Fin 3 → G) : G :=
  ⁅t 0, r 0⁆ * ⁅t 1, r 1⁆ * ⁅t 2, r 2⁆

private def erase : F →* FreeGroup Bool :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ ↦ 1))

private theorem erase_relators {r : Fin 3 → F}
    (h : markedProduct r (fun i ↦ FreeGroup.of (.inr i)) = 1) (i : Fin 3) :
    erase (r i) = 1 := by
  let keep : F →* FreeGroup (Option Bool) := FreeGroup.lift <| Sum.elim
    (fun b ↦ FreeGroup.of (some b)) (fun j ↦ if j = i then FreeGroup.of none else 1)
  let drop : FreeGroup (Option Bool) →* FreeGroup Bool :=
    FreeGroup.lift (fun b ↦ b.elim 1 FreeGroup.of)
  have comp_eq : drop.comp keep = erase := by
    ext (b | j)
    · simp [keep, drop, erase]
    · by_cases hji : j = i <;> simp [keep, drop, erase, hji]
  have hsingle : ⁅FreeGroup.of (none : Option Bool), keep (r i)⁆ = 1 := by
    have he := congrArg keep h
    simp only [markedProduct, map_mul, map_commutatorElement, map_one] at he
    fin_cases i <;> simpa [keep] using he
  obtain ⟨j, hj⟩ := FreeGroup.commute_of_iff.mp (commutatorElement_eq_one_iff_commute.mp hsingle)
  rw [← comp_eq, MonoidHom.comp_apply, ← hj]
  simp [drop]

private def equation : Monoid.Coprod F (FreeGroup (Fin 4)) :=
  let coeff (i : Alphabet) := Monoid.Coprod.inl (FreeGroup.of i)
  let var (i : Fin 4) := Monoid.Coprod.inr (FreeGroup.of i)
  markedProduct (relators (coeff (.inl false)) (coeff (.inl true)) var)
    (fun i ↦ coeff (.inr i))

private theorem eval_equation {G : Type*} [Group G] (f : F →* G) (x : Fin 4 → G) :
    Monoid.Coprod.lift f (FreeGroup.lift x) equation =
      markedProduct (relators (f (FreeGroup.of (.inl false))) (f (FreeGroup.of (.inl true))) x)
        (fun i ↦ f (FreeGroup.of (.inr i))) := by
  simp [equation, markedProduct, map_commutatorElement, map_relators, Function.comp_def]

/--
**An unsolvable equation over a free group that is solvable in every finite quotient.** There are
a free group $F$ on some set of generators, a natural number $n$ and an equation $w$ over $F$ in
the unknowns $x_0, \dots, x_{n-1}$, that is, an element $w$ of the free product of $F$ with the
free group on $x_0, \dots, x_{n-1}$, such that no $g_0, \dots, g_{n-1} \in F$ satisfy the equation
(substituting $g_i$ for $x_i$ never sends $w$ to $1$), but for every normal subgroup $N$ of finite
index in $F$ there are $h_0, \dots, h_{n-1} \in F / N$ such that substituting $h_i$ for $x_i$ and
mapping the coefficients of $w$ to their images in $F / N$ sends $w$ to $1$.

Resolved false: the Kourovka Archive answers 14.48 "No, not always", citing Coulbois and Khelif:
some equation over a free group has no solution in it but has a solution in every finite quotient.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.48 (L.
Comerford); resolution: T. Coulbois and A. Khelif, Proc. Amer. Math. Soc. 127 (1999), no. 4,
963-965, Kourovka Archive, Problem 14.48 (answer: No, not always).
-/
public theorem unsolvableEquationUnsolvableInFiniteQuotient_refuted :
    ¬ unsolvableEquationUnsolvableInFiniteQuotient := by
  intro claim
  have unsolved (x : Fin 4 → F) :
      Monoid.Coprod.lift (MonoidHom.id F) (FreeGroup.lift x) equation ≠ 1 := by
    rw [eval_equation]
    intro h
    apply no_free_solution (erase ∘ x)
    intro i
    simpa [map_relators, erase] using erase_relators h i
  obtain ⟨N, hN, hfin, hn⟩ := claim Alphabet 4 equation unsolved
  let q := QuotientGroup.mk' N
  obtain ⟨x, hx⟩ := finite_solution (q (FreeGroup.of (.inl false))) (q (FreeGroup.of (.inl true)))
  apply hn x
  simp [eval_equation, markedProduct, ← show q = QuotientGroup.mk' N from rfl, hx]

end MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48Wanted
