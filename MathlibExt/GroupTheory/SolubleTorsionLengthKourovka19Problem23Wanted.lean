/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic

/-!
# Soluble groups of torsion length greater than two (Kourovka Notebook Problem 19.23)

Kourovka Notebook, Archive of Solved Problems, Problem 19.23 (M. Chiodo, R. Vyas): `Tor₁(G)` is the
normal closure of the torsion elements of `G`, `Tor_{i+1}(G)` the preimage of `Tor₁(G / Tor_i(G))`,
and the torsion length is the least `l ≥ 1` with `G / Tor_l(G)` torsion-free (or `ω`). Does there
exist a finitely generated, or even finitely presented, soluble group with torsion length greater
than `2`?

The main result is `existsFinitelyPresentedSolubleTorsionLengthGtTwo_holds`: there is a finitely
presented soluble group of torsion length greater than `2`, proved with the polycyclic group
constructed by Leary and Minasyan as an iterated semidirect product of Klein bottle groups.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.23 (M.
Chiodo, R. Vyas). UnsolvedMath record UM-00701571 (`KOU-19.23`), dataset ulamai/UnsolvedMath v1.8.0.

The stronger alternative (finitely presented) is stated, with Mathlib's `Group.IsFinitelyPresented`.
`Tor_{i+1}(G)` is written as the normal closure of the elements with a positive power in `Tor_i(G)`,
which is the preimage of `Tor₁(G / Tor_i(G))`. Torsion length greater than `2` means `G / Tor₂(G)`
is not torsion-free (if `G / Tor₁(G)` were torsion-free, `Tor₂(G) = Tor₁(G)`).
-/

/-- **Torsion series.** For a group $G$, the torsion series of Chiodo and Vyas is the sequence of
subgroups $\mathrm{Tor}_i(G)$ of $G$ defined by $\mathrm{Tor}_0(G) = 1$, the trivial subgroup,
and, for each $i$, $\mathrm{Tor}_{i+1}(G)$ is the normal closure in $G$ of the set of elements $g$
such that $g^n \in \mathrm{Tor}_i(G)$ for some integer $n > 0$.

This is the preimage of $\mathrm{Tor}_1(G / \mathrm{Tor}_i(G))$, the normal closure of the torsion
elements of $G / \mathrm{Tor}_i(G)$, since normal closures commute with the quotient map and
$\mathrm{Tor}_i(G)$ lies in that set. -/
def torsionSeries (G : Type*) [Group G] : ℕ → Subgroup G
  | 0 => ⊥
  | i + 1 => Subgroup.normalClosure {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries G i}

/-- **Torsion length greater than two.** A group $G$ has torsion length greater than $2$ when
$G / \mathrm{Tor}_2(G)$ is not torsion-free, where $\mathrm{Tor}_2(G)$ is the second term of the
torsion series of $G$: some element $g \in G$ outside $\mathrm{Tor}_2(G)$ has a power $g^n$ with
$n > 0$ in $\mathrm{Tor}_2(G)$.

Then $G / \mathrm{Tor}_1(G)$ is not torsion-free either, so neither $1$ nor $2$ is the torsion
length of $G$. -/
def TorsionLengthGtTwo (G : Type*) [Group G] : Prop :=
  ∃ g : G, g ∉ torsionSeries G 2 ∧ ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries G 2

/-- **Kourovka Problem 19.23 (Chiodo–Vyas), finitely presented form.** The statement that there is
a finitely presented soluble group $G$ of torsion length greater than $2$, that is, such that
$G / \mathrm{Tor}_2(G)$ is not torsion-free, where $\mathrm{Tor}_2(G)$ is the second term of the
torsion series of $G$. -/
def existsFinitelyPresentedSolubleTorsionLengthGtTwo : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ Group.IsSolvable G ∧
    TorsionLengthGtTwo G

open SemidirectProduct

/-- Negation automorphism of `Multiplicative ℤ`. -/
private noncomputable def negAutZ : MulAut (Multiplicative ℤ) :=
  (AddEquiv.neg ℤ).toMultiplicative

private theorem negAutZ_apply (x : Multiplicative ℤ) :
    (negAutZ x).toAdd = -x.toAdd := rfl

private theorem negAutZ_mul_self : negAutZ * negAutZ = (1 : MulAut (Multiplicative ℤ)) := by
  ext x
  simp [negAutZ]

/-- The sign action of `Multiplicative ℤ` on itself, by parity of the exponent. -/
private noncomputable def kleinFun (q : Multiplicative ℤ) : MulAut (Multiplicative ℤ) :=
  if Even q.toAdd then 1 else negAutZ

private theorem kleinFun_apply (q p : Multiplicative ℤ) :
    (kleinFun q p).toAdd = if Even q.toAdd then p.toAdd else -p.toAdd := by
  by_cases h : Even q.toAdd <;> simp [kleinFun, h, negAutZ_apply]

private theorem kleinFun_mul (q r : Multiplicative ℤ) :
    kleinFun (q * r) = kleinFun q * kleinFun r := by
  have hsum : (q * r).toAdd = q.toAdd + r.toAdd := rfl
  have hiff : Even (q.toAdd + r.toAdd) ↔ (Even q.toAdd ↔ Even r.toAdd) := Int.even_add
  ext p
  apply Multiplicative.toAdd.injective
  change (kleinFun (q * r) p).toAdd = (kleinFun q (kleinFun r p)).toAdd
  rw [kleinFun_apply, kleinFun_apply, kleinFun_apply, hsum]
  simp only [hiff]
  by_cases hq : Even q.toAdd <;> by_cases hr : Even r.toAdd <;> simp [hq, hr]

/-- The action defining the Klein bottle group: the second factor acts by inversion. -/
private noncomputable def kleinAction : Multiplicative ℤ →* MulAut (Multiplicative ℤ) where
  toFun := kleinFun
  map_one' := by simp [kleinFun]
  map_mul' := kleinFun_mul

/-- The Klein bottle group, as a semidirect product of `ℤ` by `ℤ`. -/
private abbrev Klein := Multiplicative ℤ ⋊[kleinAction] Multiplicative ℤ

private theorem kleinAction_apply (q p : Multiplicative ℤ) :
    (kleinAction q p).toAdd = if Even q.toAdd then p.toAdd else -p.toAdd :=
  kleinFun_apply q p

/-- The product of two Klein bottle groups. -/
private abbrev KleinProd := Klein × Klein

/-- Swap the two Klein bottle factors. -/
private noncomputable def swapK : MulAut KleinProd where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := Prod.eta x ▸ rfl
  right_inv x := Prod.eta x ▸ rfl
  map_mul' _x _y := rfl

private theorem swapK_apply (x : KleinProd) : swapK x = (x.2, x.1) := rfl

private theorem swapK_sq : swapK * swapK = (1 : MulAut KleinProd) := by
  ext x <;> simp [swapK_apply]

private theorem swapK_swapK (k : KleinProd) : swapK (swapK k) = k := by cases k; rfl

private theorem neg_self_zmod2 (x : ZMod 2) : -x = x := CharTwo.neg_eq x

/-- The sum of the `a`-coordinates of the two Klein bottle factors. -/
private noncomputable def leftSum (k : KleinProd) : ℤ := k.1.left.toAdd + k.2.left.toAdd

private theorem leftSum_cast_mul (k₁ k₂ : KleinProd) :
    ((leftSum (k₁ * k₂) : ℤ) : ZMod 2) =
      (leftSum k₁ : ZMod 2) + (leftSum k₂ : ZMod 2) := by
  have h1 : ((k₁ * k₂).1.left).toAdd =
      k₁.1.left.toAdd + ((kleinAction k₁.1.right) k₂.1.left).toAdd := rfl
  have h2 : ((k₁ * k₂).2.left).toAdd =
      k₁.2.left.toAdd + ((kleinAction k₁.2.right) k₂.2.left).toAdd := rfl
  unfold leftSum
  rw [h1, h2, kleinAction_apply, kleinAction_apply]
  push_cast
  by_cases h1r : Even k₁.1.right.toAdd <;> by_cases h2r : Even k₁.2.right.toAdd <;>
    (simp [h1r, h2r]; ring)

private theorem even_iff_cast_zmod2 (a : ℤ) : Even a ↔ (a : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩

private theorem leftSum_mul (k₁ k₂ : KleinProd) :
    Even (leftSum (k₁ * k₂)) ↔ (Even (leftSum k₁) ↔ Even (leftSum k₂)) := by
  rw [even_iff_cast_zmod2, even_iff_cast_zmod2, even_iff_cast_zmod2, leftSum_cast_mul]
  set x : ZMod 2 := (leftSum k₁ : ZMod 2) with hx
  set y : ZMod 2 := (leftSum k₂ : ZMod 2) with hy
  constructor
  · intro h
    rw [add_eq_zero_iff_eq_neg, neg_self_zmod2] at h
    exact ⟨fun hh => h ▸ hh, fun hh => h.symm ▸ hh⟩
  · intro h
    by_cases hx0 : x = 0
    · rw [hx0, h.mp hx0, add_zero]
    · have hy0 : y ≠ 0 := fun hy0 => hx0 (h.mpr hy0)
      have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have hx1 : x = 1 := (htwo x).resolve_left hx0
      have hy1 : y = 1 := (htwo y).resolve_left hy0
      rw [hx1, hy1]; decide

/-- The order-two automorphism of `KleinProd` used as the action in `H2`. -/
private noncomputable def swapFun (k : KleinProd) : MulAut KleinProd :=
  if Even (leftSum k) then 1 else swapK

private theorem swapFun_swap (k : KleinProd) : swapFun (swapK k) = swapFun k := by
  unfold swapFun
  have : leftSum (swapK k) = leftSum k := by
    unfold leftSum; rw [swapK_apply]; exact add_comm _ _
  rw [this]

private theorem swapFun_mul (k₁ k₂ : KleinProd) :
    swapFun (k₁ * k₂) = swapFun k₁ * swapFun k₂ := by
  by_cases h₁ : Even (leftSum k₁) <;> by_cases h₂ : Even (leftSum k₂)
  · have h : Even (leftSum (k₁ * k₂)) :=
      (leftSum_mul k₁ k₂).mpr (iff_of_true h₁ h₂)
    simp [swapFun, h, h₁, h₂]
  · have h : ¬ Even (leftSum (k₁ * k₂)) := by
      rw [leftSum_mul]; exact fun hh => h₂ (hh.mp h₁)
    simp [swapFun, h, h₁, h₂]
  · have h : ¬ Even (leftSum (k₁ * k₂)) := by
      rw [leftSum_mul]; exact fun hh => h₁ (hh.mpr h₂)
    simp [swapFun, h, h₁, h₂]
  · have h : Even (leftSum (k₁ * k₂)) :=
      (leftSum_mul k₁ k₂).mpr (iff_of_false h₁ h₂)
    simp [swapFun, h, h₁, h₂, swapK_sq]

/-- The action of the second Klein bottle factor on the first, in the Leary–Minasyan
construction. -/
private noncomputable def swapAction : KleinProd →* MulAut KleinProd where
  toFun := swapFun
  map_one' := by
    have : leftSum (1 : KleinProd) = 0 := rfl
    simp [swapFun, this]
  map_mul' := swapFun_mul

/-- The second iterated semidirect product `H₂` of the Leary–Minasyan construction. -/
private abbrev H2 := KleinProd ⋊[swapAction] KleinProd

/-- The extension of `swapK` to `H2`, acting on the second factor only. -/
private noncomputable def beta2 : MulAut H2 where
  toFun x := ⟨x.left, swapK x.right⟩
  invFun x := ⟨x.left, swapK x.right⟩
  left_inv x := by
    apply SemidirectProduct.ext
    · rfl
    · exact swapK_swapK _
  right_inv x := by
    apply SemidirectProduct.ext
    · rfl
    · exact swapK_swapK _
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change x.left * swapAction x.right y.left = x.left * swapAction (swapK x.right) y.left
      have hsw : swapAction (swapK x.right) = swapAction x.right := swapFun_swap _
      rw [hsw]
    · change swapK (x.right * y.right) = swapK x.right * swapK y.right
      exact map_mul swapK _ _

private theorem beta2_apply (x : H2) : beta2 x = ⟨x.left, swapK x.right⟩ := rfl

private theorem beta2_sq : beta2 * beta2 = (1 : MulAut H2) := by
  ext x <;> simp [beta2_apply, swapK_apply]

/-- Torsion-freeness for a semidirect product, in the form used below. -/
private theorem torsionFree_semidirect {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (hN : ∀ x : N, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1)
    (hG : ∀ x : G, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1) :
    ∀ x : N ⋊[φ] G, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1 := by
  intro x n hn h
  have hpr : ∀ m : ℕ, (x ^ m).right = x.right ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, SemidirectProduct.mul_right, ih, pow_succ]
  have hr : x.right = 1 := by
    apply hG _ n hn
    rw [← hpr n, h]; rfl
  have hxl : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · simp [hr]
  have hpow : (x.left : N) ^ n = 1 := by
    have h2 : (SemidirectProduct.inl x.left : N ⋊[φ] G) ^ n = 1 := by rw [← hxl]; exact h
    rw [← map_pow] at h2
    exact SemidirectProduct.inl_injective (by simpa using h2)
  have hl : x.left = 1 := hN _ n hn hpow
  apply SemidirectProduct.ext
  · simp [hl]
  · simp [hr]

private theorem torsionFree_int (x : Multiplicative ℤ) (n : ℕ) (hn : 0 < n) (h : x ^ n = 1) :
    x = 1 := by
  have hpow : ∀ m : ℕ, (x ^ m).toAdd = m * x.toAdd := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      change (x ^ k * x).toAdd = (k + 1) * x.toAdd
      change (x ^ k).toAdd + x.toAdd = (k + 1) * x.toAdd
      rw [ih]; ring
  have hta : (x ^ n).toAdd = 0 := by rw [h]; rfl
  rw [hpow] at hta
  have hzero : x.toAdd = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · omega
    · exact (mul_eq_zero.mp hta).resolve_left (by omega : (n : ℤ) ≠ 0)
  exact Multiplicative.toAdd.injective (by simp [hzero])

private theorem torsionFree_prod {A B : Type*} [Group A] [Group B]
    (hA : ∀ x : A, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1)
    (hB : ∀ x : B, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1) :
    ∀ x : A × B, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1 := by
  intro x n hn h
  have h1 : x.1 ^ n = 1 := by
    have := congrArg Prod.fst h; simpa using this
  have h2 : x.2 ^ n = 1 := by
    have := congrArg Prod.snd h; simpa using this
  exact Prod.ext (hA _ n hn h1) (hB _ n hn h2)

private theorem torsionFree_Klein : ∀ x : Klein, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1 :=
  torsionFree_semidirect torsionFree_int torsionFree_int

private theorem torsionFree_K : ∀ x : KleinProd, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1 :=
  torsionFree_prod torsionFree_Klein torsionFree_Klein

private theorem torsionFree_H2 : ∀ x : H2, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1 :=
  torsionFree_semidirect torsionFree_K torsionFree_K

/-- Exactness of the swap automorphism of `KleinProd` (Lemma 2.11(iii) of Leary–Minasyan). -/
private theorem swap_exact (k : KleinProd) (h : k * swapK k = 1) :
    ∃ u : KleinProd, u⁻¹ * swapK u = k := by
  have h1 : k.1 * k.2 = 1 := by
    have := congrArg Prod.fst h; simpa [swapK_apply] using this
  have h2 : k.2 = k.1⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨(1, k.1), ?_⟩
  apply Prod.ext
  · change (1 : Klein)⁻¹ * k.1 = k.1
    rw [inv_one, one_mul]
  · change k.1⁻¹ * (1 : Klein) = k.2
    rw [mul_one, h2]

private theorem even_leftSum_inv (u : Klein) : Even (leftSum (u, u⁻¹)) := by
  have hinv : (u⁻¹).left.toAdd =
      if Even u.right.toAdd then -u.left.toAdd else u.left.toAdd := by
    rw [SemidirectProduct.inv_left]
    have e1 : ((kleinAction u.right⁻¹) u.left⁻¹).toAdd =
        if Even (u.right⁻¹).toAdd then (u.left⁻¹).toAdd else -(u.left⁻¹).toAdd :=
      kleinAction_apply _ _
    rw [e1]
    have e2 : (u.left⁻¹).toAdd = -u.left.toAdd := rfl
    rw [e2, show (u.right⁻¹).toAdd = -u.right.toAdd from rfl]
    by_cases h : Even u.right.toAdd
    · have hc : Even (-u.right.toAdd) := even_neg.mpr h
      simp [hc, h]
    · have hc : ¬ Even (-u.right.toAdd) := fun hh => h (even_neg.mp hh)
      simp [hc, h, neg_neg]
  unfold leftSum
  simp only [hinv]
  by_cases h : Even u.right.toAdd
  · simp [h]
  · simp [h]

/-- Exactness of the extension `beta2` (Lemma 2.10 of Leary–Minasyan, in this case). -/
private theorem beta2_exact (z : H2) (h : z * beta2 z = 1) :
    ∃ w : H2, w⁻¹ * beta2 w = z := by
  have hr : z.right * swapK z.right = 1 := by
    have := congrArg SemidirectProduct.right h
    simpa [beta2_apply] using this
  obtain ⟨u, hu⟩ := swap_exact z.right hr
  have hleft : z.left * swapAction z.right z.left = 1 := by
    have := congrArg SemidirectProduct.left h
    simpa [beta2_apply] using this
  have hswap : swapAction z.right = 1 := by
    have h2 : z.right.2 = z.right.1⁻¹ := eq_inv_of_mul_eq_one_right (by
      have := congrArg Prod.fst hr; simpa [swapK_apply] using this)
    have hev : Even (leftSum z.right) := by
      have : z.right = (z.right.1, z.right.1⁻¹) := by
        apply Prod.ext <;> simp [h2]
      rw [this]; exact even_leftSum_inv _
    change swapFun z.right = 1
    simp [swapFun, hev]
  rw [hswap] at hleft
  simp only [MulAut.one_apply] at hleft
  have hzleft : z.left = 1 := by
    apply torsionFree_K _ 2 (by norm_num)
    rw [pow_two]; exact hleft
  refine ⟨⟨1, u⟩, ?_⟩
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, beta2_apply, hzleft]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, beta2_apply]
    exact hu

section FPHelpers

variable {n m : ℕ} {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

/-- The generator function for the combined presentation of a semidirect product. -/
private noncomputable def fpGen (φN : FreeGroup (Fin n) →* N) (φG : FreeGroup (Fin m) →* G)
    (x : Fin n ⊕ Fin m) : N ⋊[φ] G :=
  match x with
  | Sum.inl i => inl (φN (FreeGroup.of i))
  | Sum.inr j => inr (φG (FreeGroup.of j))

private theorem fpGen_inl (φN : FreeGroup (Fin n) →* N) (φG : FreeGroup (Fin m) →* G) (i : Fin n) :
    fpGen (φ := φ) φN φG (Sum.inl i) = inl (φN (FreeGroup.of i)) := rfl

private theorem fpGen_inr (φN : FreeGroup (Fin n) →* N) (φG : FreeGroup (Fin m) →* G) (j : Fin m) :
    fpGen (φ := φ) φN φG (Sum.inr j) = inr (φG (FreeGroup.of j)) := rfl

/-- The conjugation relation for one pair of generators. -/
private noncomputable def fpWord (φN : FreeGroup (Fin n) →* N) (φG : FreeGroup (Fin m) →* G)
    (hφN : Function.Surjective φN) (p : Fin m × Fin n) : FreeGroup (Fin n ⊕ Fin m) :=
  FreeGroup.of (Sum.inr p.1) * FreeGroup.of (Sum.inl p.2) * (FreeGroup.of (Sum.inr p.1))⁻¹ *
    (FreeGroup.map Sum.inl (Function.surjInv hφN
      (φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2)))))⁻¹

private theorem fpWord_apply (φN : FreeGroup (Fin n) →* N) (φG : FreeGroup (Fin m) →* G)
    (hφN : Function.Surjective φN) (p : Fin m × Fin n) :
    φN (Function.surjInv hφN (φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2)))) =
      φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2)) :=
  Function.surjInv_eq hφN _


private theorem isFinitelyPresented_semidirect (φ : G →* MulAut N)
    [Group.IsFinitelyPresented N] [Group.IsFinitelyPresented G] :
    Group.IsFinitelyPresented (N ⋊[φ] G) := by
  classical
  obtain ⟨n, φN, hφN, hkerN⟩ := Group.IsFinitelyPresented.out (G := N)
  obtain ⟨m, φG, hφG, hkerG⟩ := Group.IsFinitelyPresented.out (G := G)
  obtain ⟨sN, hsNfin, hsN⟩ := hkerN
  obtain ⟨sG, hsGfin, hsG⟩ := hkerG
  -- The finite set of relations.
  set R : Set (FreeGroup (Fin n ⊕ Fin m)) :=
    FreeGroup.map Sum.inl '' sN ∪ FreeGroup.map Sum.inr '' sG ∪
      Set.range (fpWord (φ := φ) φN φG hφN) with hRdef
  have hRfin : R.Finite := by
    rw [hRdef]
    exact ((hsNfin.image (⇑(FreeGroup.map Sum.inl))).union
      (hsGfin.image (⇑(FreeGroup.map Sum.inr)))).union
      (Set.finite_range (fpWord (φ := φ) φN φG hφN))
  have hRfin' : Finite ↥R := hRfin
  -- The map from the free group on the combined generators.
  set Φ : FreeGroup (Fin n ⊕ Fin m) →* N ⋊[φ] G := FreeGroup.lift (fpGen (φ := φ) φN φG) with hΦdef
  have hΦinl : ∀ w : FreeGroup (Fin n),
      Φ (FreeGroup.map Sum.inl w) = inl (φN w) := by
    intro w
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · simp [Φ]
    · intro i; simp [Φ, fpGen_inl]
    · intro i ih; rw [map_inv, map_inv, map_inv, ih]; exact (map_inv _ _).symm
    · intro x y hx hy; rw [map_mul, map_mul, map_mul, hx, hy]; exact (map_mul _ _ _).symm
  have hΦinr : ∀ w : FreeGroup (Fin m),
      Φ (FreeGroup.map Sum.inr w) = inr (φG w) := by
    intro w
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · simp [Φ]
    · intro j; simp [Φ, fpGen_inr]
    · intro j ih; rw [map_inv, map_inv, map_inv, ih]; exact (map_inv _ _).symm
    · intro x y hx hy; rw [map_mul, map_mul, map_mul, hx, hy]; exact (map_mul _ _ _).symm
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨a, ha⟩ := hφN x.left
    obtain ⟨b, hb⟩ := hφG x.right
    refine ⟨FreeGroup.map Sum.inl a * FreeGroup.map Sum.inr b, ?_⟩
    rw [map_mul, hΦinl, hΦinr, ha, hb]
    exact (SemidirectProduct.mk_eq_inl_mul_inr x.right x.left).symm
  -- The relations hold in the semidirect product.
  have hRel : ∀ r ∈ R, Φ r = 1 := by
    intro r hr
    rw [hRdef] at hr
    rcases hr with hAB | hC
    · rcases hAB with hA | hB
      · obtain ⟨s, hs, rfl⟩ := hA
        rw [hΦinl]
        have : s ∈ φN.ker := by rw [← hsN]; exact Subgroup.subset_normalClosure hs
        rw [MonoidHom.mem_ker] at this
        simp [this]
      · obtain ⟨s, hs, hsr⟩ := hB
        rw [← hsr, hΦinr]
        have : s ∈ φG.ker := by rw [← hsG]; exact Subgroup.subset_normalClosure hs
        rw [MonoidHom.mem_ker] at this
        simp [this]
    · obtain ⟨p, hpr⟩ := hC
      rw [← hpr]
      show Φ (fpWord (φ := φ) φN φG hφN p) = 1
      have e1 : Φ (FreeGroup.of (Sum.inr p.1)) = inr (φG (FreeGroup.of p.1)) := by
        have hmap : FreeGroup.of (Sum.inr p.1) =
            FreeGroup.map (Sum.inr : Fin m → Fin n ⊕ Fin m) (FreeGroup.of p.1) := by simp
        rw [hmap]; exact hΦinr _
      have e2 : Φ (FreeGroup.of (Sum.inl p.2)) = inl (φN (FreeGroup.of p.2)) := by
        have hmap : FreeGroup.of (Sum.inl p.2) =
            FreeGroup.map (Sum.inl : Fin n → Fin n ⊕ Fin m) (FreeGroup.of p.2) := by simp
        rw [hmap]; exact hΦinl _
      have e3 : Φ ((FreeGroup.map Sum.inl (Function.surjInv hφN
            (φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2)))))⁻¹) =
          (inl (φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2))))⁻¹ := by
        rw [map_inv, hΦinl, fpWord_apply]
      change Φ (FreeGroup.of (Sum.inr p.1) * FreeGroup.of (Sum.inl p.2) *
          (FreeGroup.of (Sum.inr p.1))⁻¹ *
          (FreeGroup.map Sum.inl (Function.surjInv hφN
            (φ (φG (FreeGroup.of p.1)) (φN (FreeGroup.of p.2)))))⁻¹) = 1
      have hinv : (inr (φG (FreeGroup.of p.1)) : N ⋊[φ] G)⁻¹ =
          inr ((φG (FreeGroup.of p.1))⁻¹) := (map_inv _ _).symm
      rw [map_mul, map_mul, map_mul, e1, e2, e3, map_inv, e1, hinv,
        ← SemidirectProduct.inl_aut, mul_inv_cancel]
  -- The induced map out of the presented group.
  set Φ' : PresentedGroup R →* N ⋊[φ] G := PresentedGroup.toGroup hRel with hΦ'def
  have hΦ'mk : ∀ w : FreeGroup (Fin n ⊕ Fin m), Φ' (PresentedGroup.mk R w) = Φ w := by
    intro w
    rfl
  -- The factor maps.
  set πN : FreeGroup (Fin n) →* PresentedGroup R :=
    (PresentedGroup.mk R).comp (FreeGroup.map Sum.inl) with hπNdef
  have hπNker : φN.ker ≤ πN.ker := by
    rw [← hsN]
    intro w hw
    rw [MonoidHom.mem_ker]
    have hw' : FreeGroup.map Sum.inl w ∈ Subgroup.normalClosure R := by
      have h1 : FreeGroup.map (Sum.inl : Fin n → Fin n ⊕ Fin m) w ∈
          Subgroup.map (FreeGroup.map (Sum.inl : Fin n → Fin n ⊕ Fin m))
            (Subgroup.normalClosure sN) := by
        rw [Subgroup.mem_map]
        exact ⟨w, hw, rfl⟩
      have h2 := Subgroup.map_normalClosure_le sN
        (FreeGroup.map (Sum.inl : Fin n → Fin n ⊕ Fin m)) h1
      have hsub : (⇑(FreeGroup.map (Sum.inl : Fin n → Fin n ⊕ Fin m)) '' sN) ⊆ R := by
        rw [hRdef]
        exact Set.subset_union_left.trans Set.subset_union_left
      exact Subgroup.normalClosure_mono hsub h2
    have : πN w = PresentedGroup.mk R (FreeGroup.map Sum.inl w) := rfl
    rw [this]
    exact PresentedGroup.mk_eq_one_iff.mpr hw'
  set πG : FreeGroup (Fin m) →* PresentedGroup R :=
    (PresentedGroup.mk R).comp (FreeGroup.map Sum.inr) with hπGdef
  have hπGker : φG.ker ≤ πG.ker := by
    rw [← hsG]
    intro w hw
    rw [MonoidHom.mem_ker]
    have hw' : FreeGroup.map Sum.inr w ∈ Subgroup.normalClosure R := by
      have h1 : FreeGroup.map (Sum.inr : Fin m → Fin n ⊕ Fin m) w ∈
          Subgroup.map (FreeGroup.map (Sum.inr : Fin m → Fin n ⊕ Fin m))
            (Subgroup.normalClosure sG) := by
        rw [Subgroup.mem_map]
        exact ⟨w, hw, rfl⟩
      have h2 := Subgroup.map_normalClosure_le sG
        (FreeGroup.map (Sum.inr : Fin m → Fin n ⊕ Fin m)) h1
      have hsub : (⇑(FreeGroup.map (Sum.inr : Fin m → Fin n ⊕ Fin m)) '' sG) ⊆ R := by
        rw [hRdef]
        exact Set.subset_union_right.trans Set.subset_union_left
      exact Subgroup.normalClosure_mono hsub h2
    have : πG w = PresentedGroup.mk R (FreeGroup.map Sum.inr w) := rfl
    rw [this]
    exact PresentedGroup.mk_eq_one_iff.mpr hw'
  set eN : FreeGroup (Fin n) ⧸ φN.ker ≃* N :=
    QuotientGroup.quotientKerEquivOfSurjective φN hφN with heNdef
  set eG : FreeGroup (Fin m) ⧸ φG.ker ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective φG hφG with heGdef
  set fn : N →* PresentedGroup R :=
    (QuotientGroup.lift φN.ker πN hπNker).comp eN.symm.toMonoidHom with hfndef
  set fg : G →* PresentedGroup R :=
    (QuotientGroup.lift φG.ker πG hπGker).comp eG.symm.toMonoidHom with hfgdef
  have hfn : ∀ w : FreeGroup (Fin n), fn (φN w) = πN w := by
    intro w
    have he : eN.symm (φN w) = QuotientGroup.mk' φN.ker w := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change (QuotientGroup.lift φN.ker πN hπNker) (eN.symm (φN w)) = πN w
    rw [he]
    exact QuotientGroup.lift_mk _ _ _
  have hfg : ∀ w : FreeGroup (Fin m), fg (φG w) = πG w := by
    intro w
    have he : eG.symm (φG w) = QuotientGroup.mk' φG.ker w := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change (QuotientGroup.lift φG.ker πG hπGker) (eG.symm (φG w)) = πG w
    rw [he]
    exact QuotientGroup.lift_mk _ _ _
  have hπNof : ∀ i : Fin n, πN (FreeGroup.of i) = PresentedGroup.of (Sum.inl i) := by
    intro i
    simp [hπNdef, PresentedGroup.of]
  have hπGof : ∀ j : Fin m, πG (FreeGroup.of j) = PresentedGroup.of (Sum.inr j) := by
    intro j
    simp [hπGdef, PresentedGroup.of]
  -- The generator conjugation condition.
  have hgen : ∀ (j : Fin m) (i : Fin n),
      fn (φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i))) =
        fg (φG (FreeGroup.of j)) * fn (φN (FreeGroup.of i)) *
          (fg (φG (FreeGroup.of j)))⁻¹ := by
    intro j i
    have hword : PresentedGroup.mk R (fpWord (φ := φ) φN φG hφN (j, i)) = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure (by
        rw [hRdef]
        exact Set.mem_union_right _ (Set.mem_range_self (j, i))))
    have hmk : PresentedGroup.mk R (FreeGroup.map Sum.inl
          (Function.surjInv hφN (φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i))))) =
        PresentedGroup.of (Sum.inr j) * PresentedGroup.of (Sum.inl i) *
          (PresentedGroup.of (Sum.inr j))⁻¹ := by
      have h1 : fpWord (φ := φ) φN φG hφN (j, i) =
          FreeGroup.of (Sum.inr j) * FreeGroup.of (Sum.inl i) * (FreeGroup.of (Sum.inr j))⁻¹ *
            (FreeGroup.map Sum.inl (Function.surjInv hφN
              (φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i)))))⁻¹ := rfl
      rw [h1] at hword
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hword
      have h2 : (PresentedGroup.mk R) (FreeGroup.of (Sum.inr j)) =
        PresentedGroup.of (Sum.inr j) := rfl
      have h3 : (PresentedGroup.mk R) (FreeGroup.of (Sum.inl i)) =
        PresentedGroup.of (Sum.inl i) := rfl
      rw [h2, h3] at hword
      exact (mul_inv_eq_one.mp hword).symm
    have hw : φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i)) =
        φN (Function.surjInv hφN (φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i)))) :=
      (fpWord_apply (φ := φ) φN φG hφN (j, i)).symm
    rw [hw, hfn, hfg, hfn, hπNof, hπGof]
    change PresentedGroup.mk R (FreeGroup.map Sum.inl (Function.surjInv hφN
        (φ (φG (FreeGroup.of j)) (φN (FreeGroup.of i))))) =
      PresentedGroup.of (Sum.inr j) * PresentedGroup.of (Sum.inl i) *
        (PresentedGroup.of (Sum.inr j))⁻¹
    exact hmk
  -- The full conjugation condition, by induction on words.
  have hcond : ∀ g : G, ∀ n : N, fn (φ g n) = fg g * fn n * (fg g)⁻¹ := by
    intro g
    obtain ⟨w, rfl⟩ := hφG g
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · intro n
      simp
    · intro j n
      obtain ⟨w', rfl⟩ := hφN n
      refine FreeGroup.induction_on w' ?_ ?_ ?_ ?_
      · simp
      · intro i
        exact hgen j i
      · intro i ih
        rw [map_inv, map_inv, map_inv, ih, map_inv]
        group
      · intro x y hx hy
        rw [map_mul φN, map_mul (φ (φG (FreeGroup.of j))), map_mul fn, hx, hy, map_mul fn]
        group
    · intro j ih n
      have h1 : φ (φG ((FreeGroup.of j)⁻¹)) = (φ (φG (FreeGroup.of j)))⁻¹ := by
        rw [map_inv, map_inv]
      have h2 : fg (φG ((FreeGroup.of j)⁻¹)) = (fg (φG (FreeGroup.of j)))⁻¹ := by
        rw [map_inv, map_inv]
      rw [h1, h2, MulAut.inv_apply, inv_inv]
      have h3 := ih ((φ (φG (FreeGroup.of j))).symm n)
      rw [MulEquiv.apply_symm_apply] at h3
      have h4 : fn ((φ (φG (FreeGroup.of j))).symm n) =
          (fg (φG (FreeGroup.of j)))⁻¹ * fn n * fg (φG (FreeGroup.of j)) := by
        have h5 : fn n = fg (φG (FreeGroup.of j)) *
            fn ((φ (φG (FreeGroup.of j))).symm n) * (fg (φG (FreeGroup.of j)))⁻¹ := h3
        calc fn ((φ (φG (FreeGroup.of j))).symm n)
            = (fg (φG (FreeGroup.of j)))⁻¹ *
                (fg (φG (FreeGroup.of j)) *
                  fn ((φ (φG (FreeGroup.of j))).symm n) *
                  (fg (φG (FreeGroup.of j)))⁻¹) * fg (φG (FreeGroup.of j)) := by group
          _ = (fg (φG (FreeGroup.of j)))⁻¹ * fn n * fg (φG (FreeGroup.of j)) := by rw [← h5]
      exact h4
    · intro x y hx hy n
      rw [map_mul, map_mul, MulAut.mul_apply, hx, hy, map_mul]
      group
  -- The inverse map out of the semidirect product.
  set Ψ : N ⋊[φ] G →* PresentedGroup R :=
    SemidirectProduct.lift fn fg (fun g => by
      apply MonoidHom.ext
      intro n
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      exact hcond g n) with hΨdef
  have hΨinl : ∀ n : N, Ψ (inl n) = fn n := by
    intro n
    simp [Ψ]
  have hΨinr : ∀ g : G, Ψ (inr g) = fg g := by
    intro g
    simp [Ψ]
  have hcomp1 : Ψ.comp Φ' = MonoidHom.id (PresentedGroup R) := by
    apply PresentedGroup.ext
    intro x
    cases x with
    | inl i =>
      change Ψ (Φ' (PresentedGroup.of (Sum.inl i))) = PresentedGroup.of (Sum.inl i)
      rw [PresentedGroup.toGroup.of, fpGen_inl, hΨinl, hfn, hπNof]
    | inr j =>
      change Ψ (Φ' (PresentedGroup.of (Sum.inr j))) = PresentedGroup.of (Sum.inr j)
      rw [PresentedGroup.toGroup.of, fpGen_inr, hΨinr, hfg, hπGof]
  have hcomp2 : Φ'.comp Ψ = MonoidHom.id (N ⋊[φ] G) := by
    apply SemidirectProduct.hom_ext
    · apply MonoidHom.ext
      intro n
      obtain ⟨w, rfl⟩ := hφN n
      change Φ' (Ψ (inl (φN w))) = inl (φN w)
      rw [hΨinl, hfn]
      show Φ' (πN w) = inl (φN w)
      change Φ' (PresentedGroup.mk R (FreeGroup.map Sum.inl w)) = inl (φN w)
      rw [hΦ'mk, hΦinl]
    · apply MonoidHom.ext
      intro g
      obtain ⟨w, rfl⟩ := hφG g
      change Φ' (Ψ (inr (φG w))) = inr (φG w)
      rw [hΨinr, hfg]
      show Φ' (πG w) = inr (φG w)
      change Φ' (PresentedGroup.mk R (FreeGroup.map Sum.inr w)) = inr (φG w)
      rw [hΦ'mk, hΦinr]
  have hbij : Function.Bijective Φ' := by
    constructor
    · intro x y hxy
      have : Ψ (Φ' x) = Ψ (Φ' y) := congrArg Ψ hxy
      rw [show Ψ (Φ' x) = x from by
        have := MonoidHom.ext_iff.mp hcomp1 x
        simpa using this, show Ψ (Φ' y) = y from by
        have := MonoidHom.ext_iff.mp hcomp1 y
        simpa using this] at this
      exact this
    · intro y
      refine ⟨Ψ y, ?_⟩
      have := MonoidHom.ext_iff.mp hcomp2 y
      simpa using this
  exact Group.IsFinitelyPresented.equiv (MulEquiv.ofBijective Φ' hbij)



end FPHelpers

/-- Solvability passes to semidirect products. -/
private theorem isSolvable_semidirect {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    [Group.IsSolvable N] [Group.IsSolvable G] : Group.IsSolvable (N ⋊[φ] G) :=
  Group.isSolvable_of_ker_le_range (SemidirectProduct.inl (φ := φ)) SemidirectProduct.rightHom
    (SemidirectProduct.range_inl_eq_ker_rightHom.symm.le)

/-- The order-two action function: the nontrivial element of `C₂` acts by `β`. -/
private noncomputable def orderTwoFun {A : Type*} [Group A] (β : MulAut A)
    (c : Multiplicative (ZMod 2)) : MulAut A :=
  if c.toAdd = 0 then 1 else β

private theorem orderTwoFun_one {A : Type*} [Group A] (β : MulAut A) :
    orderTwoFun β 1 = 1 := rfl

private theorem orderTwoFun_c {A : Type*} [Group A] (β : MulAut A) :
    orderTwoFun β (Multiplicative.ofAdd 1) = β := ite_eq_right (by decide)

private theorem orderTwoFun_mul {A : Type*} [Group A] {β : MulAut A} (hβ : β * β = 1)
    (c d : Multiplicative (ZMod 2)) :
    orderTwoFun β (c * d) = orderTwoFun β c * orderTwoFun β d := by
  have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := by
    rcases htwo c.toAdd with h | h
    · left; exact Multiplicative.toAdd.injective (by simpa using h)
    · right; exact Multiplicative.toAdd.injective (by simpa using h)
  have hd : d = 1 ∨ d = Multiplicative.ofAdd 1 := by
    rcases htwo d.toAdd with h | h
    · left; exact Multiplicative.toAdd.injective (by simpa using h)
    · right; exact Multiplicative.toAdd.injective (by simpa using h)
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · simp [orderTwoFun]
  · simp [orderTwoFun]
  · simp [orderTwoFun]
  · have h1 : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1).toAdd = 0 := by decide
    simp [orderTwoFun, h1, hβ]

/-- The action of `C₂` on a group by an order-two automorphism. -/
private noncomputable def orderTwoAction {A : Type*} [Group A] (β : MulAut A) (hβ : β * β = 1) :
    Multiplicative (ZMod 2) →* MulAut A where
  toFun := orderTwoFun β
  map_one' := orderTwoFun_one β
  map_mul' := orderTwoFun_mul hβ

private theorem orderTwoAction_one {A : Type*} [Group A] {β : MulAut A} {hβ : β * β = 1} :
    orderTwoAction β hβ 1 = 1 := orderTwoFun_one β

private theorem orderTwoAction_c {A : Type*} [Group A] {β : MulAut A} {hβ : β * β = 1} :
    orderTwoAction β hβ (Multiplicative.ofAdd 1) = β := orderTwoFun_c β

/-- The group `G₂` of the Leary–Minasyan construction: `K ⋊ ⟨β⟩`. -/
private abbrev G2 := KleinProd ⋊[orderTwoAction swapK swapK_sq] Multiplicative (ZMod 2)

/-- The group `G₃` of the Leary–Minasyan construction: `H₂ ⋊ ⟨β₂⟩`. -/
private abbrev G3 := H2 ⋊[orderTwoAction beta2 beta2_sq] Multiplicative (ZMod 2)

/-- The nontrivial element of `C₂`, as a multiplicative group. -/
private noncomputable def cTwo : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private theorem cTwo_sq : cTwo ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  show (cTwo ^ 2).toAdd = (1 : Multiplicative (ZMod 2)).toAdd
  have : (cTwo ^ 2).toAdd = 2 * cTwo.toAdd := by
    rw [show cTwo ^ 2 = cTwo * cTwo from sq cTwo]
    rfl
  rw [this]
  decide

private theorem cTwo_cases (c : Multiplicative (ZMod 2)) : c = 1 ∨ c = cTwo := by
  have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases htwo c.toAdd with h | h
  · left; exact Multiplicative.toAdd.injective (by simpa using h)
  · right
    rw [show cTwo = Multiplicative.ofAdd 1 from rfl]
    exact Multiplicative.toAdd.injective (by simpa using h)

/-- Every torsion element of a semidirect product by `C₂` with an exact order-two
automorphism is `1` or conjugate to the generator of the `C₂` factor. This is the
content of Lemma 2.7 of Leary–Minasyan, applied through `beta2_exact` and `swap_exact`. -/
private theorem torsion_conj {A : Type*} [Group A] {β : MulAut A} {hβ : β * β = 1}
    (htf : ∀ x : A, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1)
    (hexact : ∀ z : A, z * β z = 1 → ∃ w : A, w⁻¹ * β w = z)
    (g : A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2))
    (hg : IsOfFinOrder g) :
    g = 1 ∨ ∃ h : A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2),
      h * SemidirectProduct.inr cTwo * h⁻¹ = g := by
  rcases cTwo_cases g.right with hr | hr
  · left
    have hxl : g = SemidirectProduct.inl g.left := by
      apply SemidirectProduct.ext
      · rfl
      · simp [hr]
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    have hpow : (g.left : A) ^ n = 1 := by
      have h2 : (SemidirectProduct.inl g.left :
          A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) ^ n
          = 1 := by rw [← hxl]; exact hgn
      rw [← map_pow] at h2
      exact SemidirectProduct.inl_injective (by simpa using h2)
    have hl : g.left = 1 := htf _ n hn hpow
    apply SemidirectProduct.ext
    · simp [hl]
    · simp [hr]
  · right
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    have hsq : g ^ 2 = SemidirectProduct.inl (g.left * β g.left) := by
      apply SemidirectProduct.ext
      · rw [pow_two, SemidirectProduct.mul_left, hr,
          show cTwo = Multiplicative.ofAdd 1 from rfl, orderTwoAction_c,
          SemidirectProduct.left_inl]
      · rw [pow_two, SemidirectProduct.mul_right, hr, ← sq]
        exact cTwo_sq
    have hpow : (g.left * β g.left : A) ^ n = 1 := by
      have h2 : (g ^ 2) ^ n = 1 := by
        rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, hgn, one_pow]
      rw [hsq, ← map_pow] at h2
      exact SemidirectProduct.inl_injective (by simpa using h2)
    have hprod : g.left * β g.left = 1 := htf _ n hn hpow
    obtain ⟨w, hw⟩ := hexact _ hprod
    refine ⟨(SemidirectProduct.inl w)⁻¹, ?_⟩
    have hconj : (SemidirectProduct.inr cTwo : A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) *
        SemidirectProduct.inl w = SemidirectProduct.inl (β w) * SemidirectProduct.inr cTwo := by
      apply SemidirectProduct.ext
      · simp [SemidirectProduct.mul_left, show cTwo = Multiplicative.ofAdd 1 from rfl,
          orderTwoAction_c]
      · simp [SemidirectProduct.mul_right]
    apply SemidirectProduct.ext
    · rw [inv_inv, mul_assoc, hconj, SemidirectProduct.mul_left,
        SemidirectProduct.inv_left, SemidirectProduct.mul_left]
      simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
        SemidirectProduct.left_inr,
        SemidirectProduct.inv_right, inv_one, mul_one]
      exact hw
    · rw [inv_inv]
      show (((SemidirectProduct.inl w)⁻¹ * SemidirectProduct.inr cTwo) *
        SemidirectProduct.inl w).right
        = g.right
      rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
        SemidirectProduct.right_inl, SemidirectProduct.right_inr]
      rw [hr]
      simp

/-- The first torsion term of such a semidirect product is the normal closure of the
generator of the `C₂` factor. -/
private theorem tor1_eq_normalClosure {A : Type*} [Group A] {β : MulAut A} {hβ : β * β = 1}
    (htf : ∀ x : A, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1)
    (hexact : ∀ z : A, z * β z = 1 → ∃ w : A, w⁻¹ * β w = z) :
    torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 1 =
      Subgroup.normalClosure {SemidirectProduct.inr cTwo} := by
  have hset : {g : A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2) |
        ∃ n : ℕ, 0 < n ∧ g ^ n ∈
          torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 0} =
      {g | IsOfFinOrder g} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ⟨n, hn, hgn⟩
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subgroup.mem_bot.mp hgn⟩
    · intro hg
      obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
      exact ⟨n, hn, Subgroup.mem_bot.mpr hgn⟩
  have hone : torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 1 =
      Subgroup.normalClosure {g | IsOfFinOrder g} := by
    show torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 1 = _
    rw [show torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 1 =
      Subgroup.normalClosure {g | ∃ n : ℕ, 0 < n ∧
        g ^ n ∈ torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 0} from rfl]
    rw [hset]
  rw [hone]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro g hg
    rcases torsion_conj htf hexact g hg with rfl | ⟨h, hh⟩
    · exact Subgroup.one_mem _
    · rw [← hh]
      exact Subgroup.Normal.conj_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) _
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    apply Subgroup.subset_normalClosure
    change IsOfFinOrder (SemidirectProduct.inr cTwo)
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2, by norm_num, ?_⟩
    rw [← map_pow, cTwo_sq, map_one]



/-- The `a`-generator of the Klein bottle group, of `a`-coordinate `t` and `s`-coordinate `0`. -/
private noncomputable def aKlein (t : ℤ) : Klein := ⟨Multiplicative.ofAdd t, 1⟩

/-- The `s`-generator of the Klein bottle group. -/
private noncomputable def sKlein : Klein := ⟨1, Multiplicative.ofAdd 1⟩

private theorem klein_mul_left_toAdd (x y : Klein) :
    (x * y).left.toAdd =
      x.left.toAdd + (if Even x.right.toAdd then y.left.toAdd else -y.left.toAdd) := by
  rw [SemidirectProduct.mul_left]
  change x.left.toAdd + ((kleinAction x.right) y.left).toAdd =
    x.left.toAdd + (if Even x.right.toAdd then y.left.toAdd else -y.left.toAdd)
  rw [kleinAction_apply]

private theorem klein_mul_right_toAdd (x y : Klein) :
    (x * y).right.toAdd = x.right.toAdd + y.right.toAdd := rfl

private theorem klein_inv_left_toAdd (x : Klein) :
    (x⁻¹).left.toAdd = if Even x.right.toAdd then -x.left.toAdd else x.left.toAdd := by
  rw [SemidirectProduct.inv_left, kleinAction_apply]
  have hinv : ∀ a : Multiplicative ℤ, a⁻¹.toAdd = -a.toAdd := fun _ => rfl
  by_cases h : Even x.right.toAdd <;> simp [h, hinv, even_neg]

private theorem aKlein_mul (s t : ℤ) : aKlein s * aKlein t = aKlein (s + t) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    show ((aKlein s * aKlein t).left).toAdd = (aKlein (s + t)).left.toAdd
    rw [SemidirectProduct.mul_left]
    change (Multiplicative.ofAdd s * (kleinAction 1) (Multiplicative.ofAdd t)).toAdd = s + t
    rw [map_one kleinAction, MulAut.one_apply]
    rfl
  · rfl

private theorem aKlein_inv (t : ℤ) : (aKlein t)⁻¹ = aKlein (-t) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [SemidirectProduct.inv_left]
    change ((kleinAction (1 : Multiplicative ℤ)⁻¹) (Multiplicative.ofAdd t)⁻¹).toAdd = -t
    rw [inv_one, map_one kleinAction, MulAut.one_apply]
    rfl
  · rfl

private theorem sKlein_conj (t : ℤ) :
    sKlein * aKlein t * sKlein⁻¹ = aKlein (-t) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    have hs1 : sKlein.left.toAdd = 0 := rfl
    have hs2 : sKlein.right.toAdd = 1 := rfl
    have ha1 : (aKlein t).left.toAdd = t := rfl
    have hsr : (sKlein * aKlein t).right.toAdd = 1 := by
      rw [klein_mul_right_toAdd]
      rfl
    have hinv : (sKlein⁻¹).left.toAdd = 0 := by
      rw [klein_inv_left_toAdd]
      have hodd : ¬ Even (1 : ℤ) := by decide
      simp [hs1, hs2, hodd]
    rw [klein_mul_left_toAdd, klein_mul_left_toAdd, hs1, hs2, ha1, hsr, hinv]
    have hodd : ¬ Even (1 : ℤ) := by decide
    simp [hodd, aKlein]
  · apply Multiplicative.toAdd.injective
    rw [klein_mul_right_toAdd, klein_mul_right_toAdd]
    rfl

/-- The set of `Δ`-values of the swap automorphism. -/
private noncomputable def deltaSet : Set KleinProd :=
  Set.range (fun k : KleinProd => k⁻¹ * swapK k)

/-- The normal closure `𝒩(β)` of the swap automorphism. -/
private noncomputable abbrev Nbeta : Subgroup KleinProd := Subgroup.normalClosure deltaSet

private theorem delta_mem (k : KleinProd) : k⁻¹ * swapK k ∈ Nbeta :=
  Subgroup.subset_normalClosure (Set.mem_range_self k)

private theorem conj_mem_Nbeta (g z : KleinProd) (hz : z ∈ Nbeta) : g * z * g⁻¹ ∈ Nbeta :=
  Subgroup.Normal.conj_mem _ hz g

private noncomputable def rightSum (k : KleinProd) : ℤ := k.1.right.toAdd + k.2.right.toAdd

/-- The quotient map `K → C₂ × C∞` of Lemma 2.11(ii). -/
private noncomputable def chiK : KleinProd →* Multiplicative (ZMod 2) × Multiplicative ℤ where
  toFun k := (Multiplicative.ofAdd ((leftSum k : ℤ) : ZMod 2), Multiplicative.ofAdd (rightSum k))
  map_one' := by
    apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> rfl
  map_mul' k₁ k₂ := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change ((leftSum (k₁ * k₂) : ℤ) : ZMod 2) =
        ((leftSum k₁ : ℤ) : ZMod 2) + ((leftSum k₂ : ℤ) : ZMod 2)
      exact leftSum_cast_mul k₁ k₂
    · apply Multiplicative.toAdd.injective
      change (k₁.1 * k₂.1).right.toAdd + (k₁.2 * k₂.2).right.toAdd =
        (k₁.1.right.toAdd + k₁.2.right.toAdd) + (k₂.1.right.toAdd + k₂.2.right.toAdd)
      rw [klein_mul_right_toAdd, klein_mul_right_toAdd]
      ring

private theorem chiK_swap (k : KleinProd) : chiK (swapK k) = chiK k := by
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    change ((leftSum (swapK k) : ℤ) : ZMod 2) = ((leftSum k : ℤ) : ZMod 2)
    have : leftSum (swapK k) = leftSum k := by
      unfold leftSum; rw [swapK_apply]; exact add_comm _ _
    rw [this]
  · apply Multiplicative.toAdd.injective
    change (swapK k).1.right.toAdd + (swapK k).2.right.toAdd =
      k.1.right.toAdd + k.2.right.toAdd
    rw [swapK_apply]
    exact add_comm _ _

private theorem chiK_delta (k : KleinProd) : chiK (k⁻¹ * swapK k) = 1 := by
  rw [map_mul, map_inv, chiK_swap, inv_mul_cancel]

private theorem Nbeta_le_ker_chiK : Nbeta ≤ chiK.ker := by
  have : chiK.ker.Normal := ⟨fun n hn g => by
    rw [MonoidHom.mem_ker] at hn ⊢
    rw [map_mul, map_mul, map_inv, hn]
    simp⟩
  apply Subgroup.normalClosure_le_normal
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  exact MonoidHom.mem_ker.mpr (chiK_delta k)

private theorem delta_one (u : Klein) :
    (1, u)⁻¹ * swapK (1, u) = (u, u⁻¹) := by
  apply Prod.ext
  · simp [swapK_apply]
  · simp [swapK_apply]

private theorem delta_aKlein (t : ℤ) :
    (1, aKlein t)⁻¹ * swapK (1, aKlein t) = (aKlein t, aKlein (-t)) := by
  apply Prod.ext
  · simp [swapK_apply, aKlein_inv]
  · simp [swapK_apply, aKlein_inv]

private theorem hpp (t : ℤ) : (aKlein t, aKlein t) ∈ Nbeta := by
  have hconj := conj_mem_Nbeta (1, sKlein) _ (delta_mem (1, aKlein t))
  rw [delta_aKlein] at hconj
  have heq : (1, sKlein) * (aKlein t, aKlein (-t)) * (1, sKlein)⁻¹ = (aKlein t, aKlein t) := by
    apply Prod.ext
    · simp
    · change sKlein * aKlein (-t) * sKlein⁻¹ = aKlein t
      rw [sKlein_conj, neg_neg]
  rw [heq] at hconj
  exact hconj

private theorem hp2 (t : ℤ) : (aKlein (t + t), 1) ∈ Nbeta := by
  have h := Subgroup.mul_mem _ (hpp t) (delta_mem (1, aKlein t))
  rw [delta_aKlein] at h
  have heq : (aKlein t, aKlein t) * (aKlein t, aKlein (-t)) = (aKlein (t + t), 1) := by
    apply Prod.ext
    · exact aKlein_mul t t
    · change aKlein t * aKlein (-t) = 1
      rw [← aKlein_inv, mul_inv_cancel]
  rw [heq] at h
  exact h

private theorem h1w (t : ℤ) : (1, aKlein (t + t)) ∈ Nbeta := by
  have h := Subgroup.mul_mem _ (hp2 t) (delta_mem (aKlein (t + t), 1))
  have hdelta : (aKlein (t + t), 1)⁻¹ * swapK (aKlein (t + t), 1) =
      (aKlein (-(t + t)), aKlein (t + t)) := by
    apply Prod.ext
    · simp [swapK_apply, aKlein_inv]
    · simp [swapK_apply, aKlein_inv]
  rw [hdelta] at h
  have heq : (aKlein (t + t), 1) * (aKlein (-(t + t)), aKlein (t + t)) =
      (1, aKlein (t + t)) := by
    apply Prod.ext
    · change aKlein (t + t) * aKlein (-(t + t)) = 1
      rw [← aKlein_inv, mul_inv_cancel]
    · simp
  rw [heq] at h
  exact h

/-- The kernel of `chiK` is exactly `𝒩(β)` (Lemma 2.11(ii)). -/
private theorem ker_chiK_eq_Nbeta : chiK.ker = Nbeta := by
  apply le_antisymm
  · intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hleft : Even (leftSum k) := by
      have h1 : ((leftSum k : ℤ) : ZMod 2) = 0 := by
        have := congrArg Prod.fst hk
        exact Multiplicative.toAdd.injective this
      exact (even_iff_cast_zmod2 _).mpr h1
    have hright : k.1.right.toAdd + k.2.right.toAdd = 0 := by
      have h1 : rightSum k = 0 := by
        have := congrArg Prod.snd hk
        exact Multiplicative.toAdd.injective this
      exact h1
    have hright2 : k.2.right = (k.1.right)⁻¹ := by
      apply Multiplicative.toAdd.injective
      show k.2.right.toAdd = ((k.1.right)⁻¹).toAdd
      have : ((k.1.right)⁻¹).toAdd = -k.1.right.toAdd := rfl
      rw [this]
      omega
    -- The element `w = k.1 * k.2` has trivial right coordinate and even left coordinate.
    set w : Klein := k.1 * k.2 with hwdef
    have hwright : w.right = 1 := by
      apply Multiplicative.toAdd.injective
      rw [klein_mul_right_toAdd, hright]
      rfl
    have hwleft : Even w.left.toAdd := by
      rw [hwdef, klein_mul_left_toAdd]
      by_cases h : Even k.1.right.toAdd
      · simp only [h, ite_true]
        unfold leftSum at hleft
        exact hleft
      · have hiff : Even (k.1.left.toAdd - k.2.left.toAdd) ↔ Even (leftSum k) := by
          unfold leftSum
          rw [sub_eq_add_neg, Int.even_add, even_neg, Int.even_add]
        simp only [h, ite_false] at *
        exact hiff.mpr hleft
    obtain ⟨t, ht⟩ := hwleft
    have hw_eq : w = aKlein (t + t) := by
      apply SemidirectProduct.ext
      · apply Multiplicative.toAdd.injective
        show w.left.toAdd = (aKlein (t + t)).left.toAdd
        rw [ht]
        rfl
      · rw [hwright]
        rfl
    have hdecomp : k = (k.1, (k.1)⁻¹) * (1, w) := by
      apply Prod.ext
      · simp
      · change k.2 = (k.1)⁻¹ * w
        rw [hwdef]
        exact (inv_mul_cancel_left k.1 k.2).symm
    have hfirst : (k.1, (k.1)⁻¹) ∈ Nbeta := by
      have h := delta_mem (1, k.1)
      rw [delta_one] at h
      exact h
    have hsecond : (1, w) ∈ Nbeta := by
      rw [hw_eq]
      exact h1w t
    rw [hdecomp]
    exact Subgroup.mul_mem _ hfirst hsecond
  · exact Nbeta_le_ker_chiK



/-- The normal closure of the `Δ`-elements maps into the first torsion term. -/
private theorem inl_delta_mem_tor1 {A : Type*} [Group A] {β : MulAut A} {hβ : β * β = 1}
    (htf : ∀ x : A, ∀ n : ℕ, 0 < n → x ^ n = 1 → x = 1)
    (hexact : ∀ z : A, z * β z = 1 → ∃ w : A, w⁻¹ * β w = z) (z : A) :
    SemidirectProduct.inl (z⁻¹ * β z) ∈
      torsionSeries (A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) 1 := by
  have hswap : (SemidirectProduct.inl (β z) :
      A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) =
      SemidirectProduct.inr cTwo * SemidirectProduct.inl z *
        (SemidirectProduct.inr cTwo)⁻¹ := by
    have h := SemidirectProduct.inl_aut (φ := orderTwoAction β hβ) cTwo z
    rw [show cTwo = Multiplicative.ofAdd 1 from rfl, orderTwoAction_c] at h
    have hinv : (SemidirectProduct.inr ((Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹) :
        A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)) =
        (SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ := map_inv _ _
    rw [hinv, show (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = cTwo from rfl] at h
    exact h
  rw [tor1_eq_normalClosure htf hexact, map_mul, hswap, map_inv]
  rw [show (SemidirectProduct.inl z)⁻¹ *
        (SemidirectProduct.inr cTwo * SemidirectProduct.inl z *
          (SemidirectProduct.inr cTwo)⁻¹) =
      ((SemidirectProduct.inl z)⁻¹ * SemidirectProduct.inr cTwo * SemidirectProduct.inl z) *
        (SemidirectProduct.inr cTwo)⁻¹ from by group]
  apply Subgroup.mul_mem _
  · have hc := Subgroup.Normal.conj_mem (SemidirectProduct.inr cTwo)
      (Subgroup.subset_normalClosure (Set.mem_singleton
        (SemidirectProduct.inr cTwo :
          A ⋊[orderTwoAction β hβ] Multiplicative (ZMod 2)))) (SemidirectProduct.inl z)⁻¹
    rw [inv_inv] at hc
    exact hc
  · exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _))

/-- The parity homomorphism `K → C₂`. -/
private noncomputable def parityHom : KleinProd →* Multiplicative (ZMod 2) where
  toFun k := Multiplicative.ofAdd ((leftSum k : ℤ) : ZMod 2)
  map_one' := rfl
  map_mul' k₁ k₂ := by
    apply Multiplicative.toAdd.injective
    change ((leftSum (k₁ * k₂) : ℤ) : ZMod 2) =
      ((leftSum k₁ : ℤ) : ZMod 2) + ((leftSum k₂ : ℤ) : ZMod 2)
    exact leftSum_cast_mul k₁ k₂

private theorem parityHom_swap (k : KleinProd) : parityHom (swapK k) = parityHom k := by
  apply Multiplicative.toAdd.injective
  change ((leftSum (swapK k) : ℤ) : ZMod 2) = ((leftSum k : ℤ) : ZMod 2)
  have : leftSum (swapK k) = leftSum k := by
    unfold leftSum; rw [swapK_apply]; exact add_comm _ _
  rw [this]

private theorem chiK_swapFun (k y : KleinProd) : chiK (swapFun k y) = chiK y := by
  by_cases h : Even (leftSum k)
  · simp [swapFun, h]
  · simp [swapFun, h, chiK_swap]

private theorem chiK_orderTwo (c : Multiplicative (ZMod 2)) (y : KleinProd) :
    chiK ((orderTwoAction swapK swapK_sq) c y) = chiK y := by
  rcases cTwo_cases c with rfl | rfl
  · rw [orderTwoAction_one]
    simp
  · rw [show cTwo = Multiplicative.ofAdd 1 from rfl, orderTwoAction_c, chiK_swap]

/-- The quotient map `G₂ → C₂ × C∞`. -/
private noncomputable def chi2 : G2 →* Multiplicative (ZMod 2) × Multiplicative ℤ where
  toFun x := chiK x.left
  map_one' := by simp
  map_mul' x y := by
    change chiK ((x * y).left) = chiK x.left * chiK y.left
    rw [SemidirectProduct.mul_left, map_mul, chiK_orderTwo]

private theorem chi2_inr (ε : Multiplicative (ZMod 2)) :
    chi2 (SemidirectProduct.inr ε) = 1 := by
  change chiK (SemidirectProduct.inr ε).left = 1
  simp

/-- The kernel of `chi2` is the first torsion term of `G₂`. -/
private theorem ker_chi2_eq_tor1 : chi2.ker = torsionSeries G2 1 := by
  have htor1 : torsionSeries G2 1 =
      Subgroup.normalClosure {SemidirectProduct.inr cTwo} :=
    tor1_eq_normalClosure torsionFree_K swap_exact
  have : chi2.ker.Normal := ⟨fun n hn g => by
    rw [MonoidHom.mem_ker] at hn ⊢
    rw [map_mul, map_mul, map_inv, hn]
    simp⟩
  apply le_antisymm
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hleft : y.left ∈ Nbeta := by
      rw [← ker_chiK_eq_Nbeta, MonoidHom.mem_ker]
      exact hy
    have hmap : Subgroup.map (SemidirectProduct.inl (N := KleinProd)
        (G := Multiplicative (ZMod 2)) (φ := orderTwoAction swapK swapK_sq)) Nbeta ≤
        (Subgroup.normalClosure {SemidirectProduct.inr cTwo} : Subgroup G2) := by
      refine le_trans (Subgroup.map_normalClosure_le deltaSet _) ?_
      apply Subgroup.normalClosure_le_normal
      intro x hx
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨u, rfl⟩ := hk
      change SemidirectProduct.inl (u⁻¹ * swapK u) ∈
        (Subgroup.normalClosure {SemidirectProduct.inr cTwo} : Subgroup G2)
      rw [← htor1]
      exact inl_delta_mem_tor1 (hβ := swapK_sq) torsionFree_K swap_exact u
    have hinl : SemidirectProduct.inl y.left ∈
        (Subgroup.normalClosure {SemidirectProduct.inr cTwo} : Subgroup G2) :=
      hmap (Subgroup.mem_map.mpr ⟨y.left, hleft, rfl⟩)
    have hy_eq : y = SemidirectProduct.inl y.left * SemidirectProduct.inr y.right := by
      apply SemidirectProduct.ext
      · simp
      · simp
    rw [htor1, hy_eq]
    apply Subgroup.mul_mem _
    · exact hinl
    · rcases cTwo_cases y.right with hr | hr
      · rw [hr]; simp
      · rw [hr]
        exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  · rw [htor1]
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact MonoidHom.mem_ker.mpr (chi2_inr cTwo)



private theorem rightSum_mul (a b : KleinProd) :
    rightSum (a * b) = rightSum a + rightSum b := by
  change (a.1 * b.1).right.toAdd + (a.2 * b.2).right.toAdd =
    (a.1.right.toAdd + a.2.right.toAdd) + (b.1.right.toAdd + b.2.right.toAdd)
  rw [klein_mul_right_toAdd, klein_mul_right_toAdd]
  ring

private theorem rightSum_swap (k : KleinProd) : rightSum (swapK k) = rightSum k := by
  unfold rightSum; rw [swapK_apply]; exact add_comm _ _

private theorem swapAction_eq_parity (k : KleinProd) :
    swapAction k = orderTwoAction swapK swapK_sq (parityHom k) := by
  change swapFun k = orderTwoFun swapK (parityHom k)
  by_cases h : Even (leftSum k)
  · have h2 : (parityHom k).toAdd = 0 := (even_iff_cast_zmod2 _).mp h
    change (if Even (leftSum k) then (1 : MulAut KleinProd) else swapK) =
      (if (parityHom k).toAdd = 0 then 1 else swapK)
    rw [ite_eq_left h, ite_eq_left h2]
  · have h2 : (parityHom k).toAdd ≠ 0 := fun hh => h ((even_iff_cast_zmod2 _).mpr hh)
    change (if Even (leftSum k) then (1 : MulAut KleinProd) else swapK) =
      (if (parityHom k).toAdd = 0 then 1 else swapK)
    rw [ite_eq_right h, ite_eq_right h2]

/-- The first component of the quotient map `G₃ → G₂ × C∞`. -/
private noncomputable def psiFn : H2 →* G2 × Multiplicative ℤ where
  toFun z := (⟨z.left, parityHom z.right⟩, Multiplicative.ofAdd (rightSum z.right))
  map_one' := by
    apply Prod.ext
    · apply SemidirectProduct.ext <;> rfl
    · rfl
  map_mul' z₁ z₂ := by
    apply Prod.ext
    · apply SemidirectProduct.ext
      · change z₁.left * swapAction z₁.right z₂.left =
          z₁.left * (orderTwoAction swapK swapK_sq) (parityHom z₁.right) z₂.left
        rw [swapAction_eq_parity]
      · change parityHom (z₁.right * z₂.right) = parityHom z₁.right * parityHom z₂.right
        exact map_mul _ _ _
    · change Multiplicative.ofAdd (rightSum (z₁ * z₂).right) =
        Multiplicative.ofAdd (rightSum z₁.right) * Multiplicative.ofAdd (rightSum z₂.right)
      rw [show (z₁ * z₂).right = z₁.right * z₂.right from rfl, rightSum_mul, ofAdd_add]

private theorem psiFn_beta2 (z : H2) : psiFn (beta2 z) = psiFn z := by
  apply Prod.ext
  · apply SemidirectProduct.ext
    · rfl
    · exact parityHom_swap _
  · change Multiplicative.ofAdd (rightSum (swapK z.right)) =
      Multiplicative.ofAdd (rightSum z.right)
    rw [rightSum_swap]

/-- The quotient map `ψ : G₃ → G₂ × C∞`, with kernel `Tor₁(G₃)`. -/
private noncomputable def psi : G3 →* G2 × Multiplicative ℤ :=
  SemidirectProduct.lift psiFn 1 (fun c => by
    apply MonoidHom.ext
    intro z
    rcases cTwo_cases c with rfl | rfl
    · simp [orderTwoAction_one]
    · simp [show cTwo = Multiplicative.ofAdd 1 from rfl, orderTwoAction_c, psiFn_beta2])

private theorem psi_apply (x : G3) : psi x = psiFn x.left := by
  change psiFn x.left * 1 = psiFn x.left
  exact mul_one _

/-- The `Δ`-set of `beta2` in `H₂`. -/
private noncomputable def delta2Set : Set H2 := Set.range (fun z : H2 => z⁻¹ * beta2 z)

/-- The normal closure `𝒩(β₂)` in `H₂`. -/
private noncomputable abbrev Nbeta2 : Subgroup H2 := Subgroup.normalClosure delta2Set

private theorem inr_delta_mem_Nbeta2 (u : KleinProd) :
    SemidirectProduct.inr (u⁻¹ * swapK u) ∈ Nbeta2 := by
  have heq : SemidirectProduct.inr (u⁻¹ * swapK u) =
      (SemidirectProduct.inr u)⁻¹ * beta2 (SemidirectProduct.inr u) := by
    apply SemidirectProduct.ext
    · show (SemidirectProduct.inr (u⁻¹ * swapK u)).left =
        ((SemidirectProduct.inr u)⁻¹ * beta2 (SemidirectProduct.inr u)).left
      rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left]
      simp [beta2_apply]
    · show (SemidirectProduct.inr (u⁻¹ * swapK u)).right =
        ((SemidirectProduct.inr u)⁻¹ * beta2 (SemidirectProduct.inr u)).right
      rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, beta2_apply]
      simp
  rw [heq]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

private theorem inr_mem_Nbeta2_of_mem_Nbeta {k : KleinProd} (hk : k ∈ Nbeta) :
    SemidirectProduct.inr k ∈ Nbeta2 := by
  have hmap : Subgroup.map (SemidirectProduct.inr (N := KleinProd) (G := KleinProd)
      (φ := swapAction)) Nbeta ≤ Nbeta2 := by
    refine le_trans (Subgroup.map_normalClosure_le deltaSet _) ?_
    apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨u, rfl⟩ := ha
    exact inr_delta_mem_Nbeta2 u
  exact hmap (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The kernel of `ψ` is the first torsion term of `G₃`. -/
private theorem ker_psi_eq_tor1 : psi.ker = torsionSeries G3 1 := by
  have htor1 : torsionSeries G3 1 =
      Subgroup.normalClosure {SemidirectProduct.inr cTwo} :=
    tor1_eq_normalClosure torsionFree_H2 beta2_exact
  have : psi.ker.Normal := ⟨fun n hn g => by
    rw [MonoidHom.mem_ker] at hn ⊢
    rw [map_mul, map_mul, map_inv, hn]
    simp⟩
  apply le_antisymm
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hfn : psiFn y.left = 1 := by rw [psi_apply] at hy; exact hy
    have h1 : y.left.left = 1 :=
      congrArg SemidirectProduct.left (congrArg Prod.fst hfn)
    have hpar : parityHom y.left.right = 1 :=
      congrArg SemidirectProduct.right (congrArg Prod.fst hfn)
    have hrs : rightSum y.left.right = 0 :=
      congrArg Multiplicative.toAdd (congrArg Prod.snd hfn)
    have hchi : chiK y.left.right = 1 := by
      apply Prod.ext
      · exact hpar
      · change Multiplicative.ofAdd (rightSum y.left.right) = 1
        rw [hrs]
        rfl
    have hk : y.left.right ∈ Nbeta := by
      rw [← ker_chiK_eq_Nbeta, MonoidHom.mem_ker]
      exact hchi
    have hleft : y.left ∈ Nbeta2 := by
      have heq : y.left = SemidirectProduct.inr y.left.right := by
        apply SemidirectProduct.ext
        · exact h1
        · rfl
      rw [heq]
      exact inr_mem_Nbeta2_of_mem_Nbeta hk
    have hinl : SemidirectProduct.inl y.left ∈ torsionSeries G3 1 := by
      have hmap : Subgroup.map (SemidirectProduct.inl (N := H2)
          (G := Multiplicative (ZMod 2)) (φ := orderTwoAction beta2 beta2_sq)) Nbeta2 ≤
          torsionSeries G3 1 := by
        rw [htor1]
        refine le_trans (Subgroup.map_normalClosure_le delta2Set _) ?_
        apply Subgroup.normalClosure_le_normal
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        obtain ⟨w, rfl⟩ := hz
        change SemidirectProduct.inl (w⁻¹ * beta2 w) ∈
          (Subgroup.normalClosure {SemidirectProduct.inr cTwo} : Subgroup G3)
        rw [← htor1]
        exact inl_delta_mem_tor1 (hβ := beta2_sq) torsionFree_H2 beta2_exact w
      exact hmap (Subgroup.mem_map.mpr ⟨y.left, hleft, rfl⟩)
    have hy_eq : y = SemidirectProduct.inl y.left * SemidirectProduct.inr y.right := by
      apply SemidirectProduct.ext <;> simp
    rw [hy_eq]
    apply Subgroup.mul_mem _
    · exact hinl
    · rcases cTwo_cases y.right with hr | hr
      · rw [hr]; simp
      · rw [hr, htor1]
        exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  · rw [htor1]
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact MonoidHom.mem_ker.mpr (by
      rw [psi_apply]
      change psiFn (1 : H2) = 1
      exact map_one _)



/-- The first torsion term is the normal closure of the torsion elements. -/
private theorem tor1_eq_torsionSet {H : Type*} [Group H] :
    torsionSeries H 1 = Subgroup.normalClosure {g : H | IsOfFinOrder g} := by
  have hset : {g : H | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries H 0} = {g | IsOfFinOrder g} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ⟨n, hn, hgn⟩
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subgroup.mem_bot.mp hgn⟩
    · intro hg
      obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
      exact ⟨n, hn, Subgroup.mem_bot.mpr hgn⟩
  change torsionSeries H 1 = _
  rw [show torsionSeries H 1 = Subgroup.normalClosure
    {g | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries H 0} from rfl, hset]

/-- The `b`-generator of the Klein bottle group, of `a`-coordinate `0` and `s`-coordinate `m`. -/
private noncomputable def bKlein (m : ℤ) : Klein := ⟨1, Multiplicative.ofAdd m⟩

private theorem psi_surjective : Function.Surjective psi := by
  intro q
  obtain ⟨⟨k, ε⟩, z⟩ := q
  rcases cTwo_cases ε with rfl | rfl
  · refine ⟨SemidirectProduct.inl ⟨k, (aKlein 0, bKlein z.toAdd)⟩, ?_⟩
    rw [psi_apply]
    apply Prod.ext
    · apply SemidirectProduct.ext
      · rfl
      · change parityHom (aKlein 0, bKlein z.toAdd) = 1
        rfl
    · apply Multiplicative.toAdd.injective
      exact zero_add _
  · refine ⟨SemidirectProduct.inl ⟨k, (aKlein 1, bKlein z.toAdd)⟩, ?_⟩
    rw [psi_apply]
    apply Prod.ext
    · apply SemidirectProduct.ext
      · rfl
      · change parityHom (aKlein 1, bKlein z.toAdd) = cTwo
        rfl
    · apply Multiplicative.toAdd.injective
      exact zero_add _

/-- The second torsion term of `G₃` is the preimage of the first torsion term of the quotient. -/
private theorem tor2_eq_comap :
    torsionSeries G3 2 = Subgroup.comap psi (torsionSeries (G2 × Multiplicative ℤ) 1) := by
  have h2 : torsionSeries G3 2 = Subgroup.normalClosure
      {g : G3 | ∃ n : ℕ, 0 < n ∧ g ^ n ∈ torsionSeries G3 1} := rfl
  have hTor1le : torsionSeries G3 1 ≤ torsionSeries G3 2 := by
    rw [tor1_eq_normalClosure torsionFree_H2 beta2_exact, h2]
    apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact Subgroup.subset_normalClosure ⟨2, by norm_num, by
      rw [← map_pow, cTwo_sq, map_one]
      exact Subgroup.one_mem _⟩
  have hmem_of_psi_eq : ∀ {u v : G3}, psi u = psi v → u ∈ torsionSeries G3 2 →
      v ∈ torsionSeries G3 2 := by
    intro u v huv hu
    have hker : u⁻¹ * v ∈ torsionSeries G3 1 := by
      rw [← ker_psi_eq_tor1, MonoidHom.mem_ker]
      rw [map_mul, map_inv, huv, inv_mul_cancel]
    have := Subgroup.mul_mem _ hu (hTor1le hker)
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at this
  have : (torsionSeries (G2 × Multiplicative ℤ) 1).Normal := by
    rw [tor1_eq_torsionSet]
    infer_instance
  have : (Subgroup.comap psi (torsionSeries (G2 × Multiplicative ℤ) 1)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_comap] at hn ⊢
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.Normal.conj_mem _ hn _⟩
  have : (torsionSeries G3 2).Normal := by
    rw [h2]
    infer_instance
  apply le_antisymm
  · rw [h2]
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨n, hn, hgn⟩ := hg
    change g ∈ Subgroup.comap psi (torsionSeries (G2 × Multiplicative ℤ) 1)
    rw [Subgroup.mem_comap, tor1_eq_torsionSet (H := G2 × Multiplicative ℤ)]
    apply Subgroup.subset_normalClosure
    have h1 : psi (g ^ n) = 1 := by
      have : g ^ n ∈ psi.ker := ker_psi_eq_tor1.symm ▸ hgn
      exact MonoidHom.mem_ker.mp this
    change IsOfFinOrder (psi g)
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, by rw [← map_pow, h1]⟩
  · intro y hy
    rw [Subgroup.mem_comap] at hy
    have key : ∀ q : G2 × Multiplicative ℤ, q ∈ torsionSeries (G2 × Multiplicative ℤ) 1 →
        ∀ v : G3, psi v = q → v ∈ torsionSeries G3 2 := by
      intro q hq v hv
      rw [tor1_eq_torsionSet] at hq
      refine Subgroup.closure_induction (p := fun q _ => ∀ v : G3, psi v = q →
        v ∈ torsionSeries G3 2) ?_ ?_ ?_ ?_ hq v hv
      · intro x hx v hv
        obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
        obtain ⟨a, ha⟩ := isConj_iff.mp hconj
        rw [← ha] at hv
        obtain ⟨aL, haL⟩ := psi_surjective a
        obtain ⟨tL, htL⟩ := psi_surjective t
        obtain ⟨n, hn, htn⟩ := isOfFinOrder_iff_pow_eq_one.mp ht
        have ht2 : tL ∈ torsionSeries G3 2 := by
          apply Subgroup.subset_normalClosure
          refine ⟨n, hn, ?_⟩
          have h1 : psi (tL ^ n) = 1 := by
            rw [map_pow, htL]
            exact htn
          exact ker_psi_eq_tor1.symm ▸ MonoidHom.mem_ker.mpr h1
        have hconj : aL * tL * aL⁻¹ ∈ torsionSeries G3 2 :=
          Subgroup.Normal.conj_mem _ ht2 _
        apply hmem_of_psi_eq (u := aL * tL * aL⁻¹) (v := v) _ hconj
        rw [map_mul, map_mul, map_inv, haL, htL]
        exact hv.symm
      · intro v hv
        apply hTor1le
        rw [← ker_psi_eq_tor1, MonoidHom.mem_ker]
        exact hv
      · intro x y _ _ hx hy v hv
        obtain ⟨xL, hxL⟩ := psi_surjective x
        obtain ⟨yL, hyL⟩ := psi_surjective y
        apply hmem_of_psi_eq (u := xL * yL) (v := v) _ (Subgroup.mul_mem _ (hx xL hxL) (hy yL hyL))
        rw [map_mul, hxL, hyL]
        exact hv.symm
      · intro x _ hx v hv
        obtain ⟨xL, hxL⟩ := psi_surjective x
        apply hmem_of_psi_eq (u := xL⁻¹) (v := v) _ (Subgroup.inv_mem _ (hx xL hxL))
        rw [map_inv, hxL]
        exact hv.symm
    exact key _ hy y rfl

/-- The witness `a`-generator in the first Klein bottle factor. -/
private noncomputable def witnessG : KleinProd := (aKlein 1, 1)

/-- The witness element of `G₃`: the `a`-generator, of infinite order in `G₃ / Tor₂(G₃)`. -/
private noncomputable def witness : G3 :=
  SemidirectProduct.inl (SemidirectProduct.inl witnessG)

private theorem psi_witness :
    psi witness = (⟨witnessG, (1 : Multiplicative (ZMod 2))⟩, (1 : Multiplicative ℤ)) := by
  rw [psi_apply]
  change psiFn (SemidirectProduct.inl witnessG) = _
  apply Prod.ext
  · apply SemidirectProduct.ext
    · rfl
    · change parityHom (1 : KleinProd) = 1
      rfl
  · rfl

private theorem witness_not_mem : witness ∉ torsionSeries G3 2 := by
  intro hmem
  rw [tor2_eq_comap, Subgroup.mem_comap] at hmem
  have hmapfst : Subgroup.map (MonoidHom.fst G2 (Multiplicative ℤ))
      (torsionSeries (G2 × Multiplicative ℤ) 1) ≤ torsionSeries G2 1 := by
    rw [tor1_eq_torsionSet, tor1_eq_torsionSet]
    refine le_trans (Subgroup.map_normalClosure_le _ _) ?_
    apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    apply Subgroup.subset_normalClosure
    obtain ⟨n, hn, hqn⟩ := isOfFinOrder_iff_pow_eq_one.mp hq
    change IsOfFinOrder (MonoidHom.fst G2 (Multiplicative ℤ) q)
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    rw [← map_pow]
    exact congrArg Prod.fst hqn
  have hfst : (⟨witnessG, (1 : Multiplicative (ZMod 2))⟩ : G2) ∈ torsionSeries G2 1 := by
    apply hmapfst
    apply Subgroup.mem_map.mpr
    exact ⟨psi witness, hmem, by rw [psi_witness]; rfl⟩
  rw [← ker_chi2_eq_tor1, MonoidHom.mem_ker] at hfst
  have hchi : chiK witnessG = 1 := hfst
  have h1 : ((leftSum witnessG : ℤ) : ZMod 2) = 0 :=
    congrArg Multiplicative.toAdd (congrArg Prod.fst hchi)
  have hls : leftSum witnessG = 1 := rfl
  rw [hls, Int.cast_one] at h1
  exact one_ne_zero h1

private theorem witness_sq_mem : witness ^ 2 ∈ torsionSeries G3 2 := by
  rw [tor2_eq_comap, Subgroup.mem_comap]
  have hb2 : (⟨witnessG, (1 : Multiplicative (ZMod 2))⟩ : G2) ^ 2 ∈ torsionSeries G2 1 := by
    rw [← ker_chi2_eq_tor1, MonoidHom.mem_ker]
    have hchi2b : chi2 (⟨witnessG, (1 : Multiplicative (ZMod 2))⟩ : G2) =
        (Multiplicative.ofAdd 1, (1 : Multiplicative ℤ)) := by
      apply Prod.ext
      · change Multiplicative.ofAdd ((leftSum witnessG : ℤ) : ZMod 2) = Multiplicative.ofAdd 1
        rw [show leftSum witnessG = 1 from rfl, Int.cast_one]
      · rfl
    rw [map_pow, hchi2b]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change ((Multiplicative.ofAdd (1 : ZMod 2)) ^ 2).toAdd = (1 : Multiplicative (ZMod 2)).toAdd
      change (1 : ZMod 2) + 1 = 0
      decide
    · simp
  have hmapinl : Subgroup.map (MonoidHom.inl G2 (Multiplicative ℤ))
      (torsionSeries G2 1) ≤ torsionSeries (G2 × Multiplicative ℤ) 1 := by
    rw [tor1_eq_torsionSet, tor1_eq_torsionSet]
    refine le_trans (Subgroup.map_normalClosure_le _ _) ?_
    apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    apply Subgroup.subset_normalClosure
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    change IsOfFinOrder (MonoidHom.inl G2 (Multiplicative ℤ) g)
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, by rw [← map_pow, hgn, map_one]⟩
  have hmem : (psi witness ^ 2) ∈ torsionSeries (G2 × Multiplicative ℤ) 1 := by
    have hpsi2 : psi witness ^ 2 = (MonoidHom.inl G2 (Multiplicative ℤ))
        ((⟨witnessG, (1 : Multiplicative (ZMod 2))⟩ : G2) ^ 2) := by
      rw [psi_witness]
      rfl
    rw [hpsi2]
    exact hmapinl (Subgroup.mem_map.mpr ⟨_, hb2, rfl⟩)
  rw [← map_pow] at hmem
  exact hmem

/--
Resolved true: the Kourovka Archive answers 19.23 "Yes, such groups exist"; Leary and Minasyan
(Theorem 2.14) construct polycyclic groups, which are finitely presented and soluble, of every
torsion length `n ≥ 1`, in particular of torsion length `3`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 19.23 (M. Chiodo, R. Vyas); resolution: I. J. Leary and
A. Minasyan, A note on torsion length and torsion subgroups, J. Group Theory 26 (2023), no. 4,
741-750 (arXiv:2112.14546), Theorem 2.14: for every integer n ≥ 1 there is a polycyclic group of
torsion length n (their torsion length counts G₀ = G, G_{n+1} = G_n / Tor(G_n) from 0 and agrees
with the Notebook's for n ≥ 1); Kourovka Archive, Problem 19.23: Yes, such groups exist,
https://arxiv.org/abs/2112.14546.
-/
theorem existsFinitelyPresentedSolubleTorsionLengthGtTwo_holds :
    existsFinitelyPresentedSolubleTorsionLengthGtTwo := by
  refine ⟨G3, inferInstance, ?_, ?_, ?_⟩
  · have : Group.IsFinitelyPresented Klein := isFinitelyPresented_semidirect kleinAction
    have : Group.IsFinitelyPresented (Klein ⋊[1] Klein) :=
      isFinitelyPresented_semidirect (1 : Klein →* MulAut Klein)
    have : Group.IsFinitelyPresented KleinProd :=
      Group.IsFinitelyPresented.equiv SemidirectProduct.mulEquivProd
    have : Group.IsFinitelyPresented H2 := isFinitelyPresented_semidirect swapAction
    exact isFinitelyPresented_semidirect (orderTwoAction beta2 beta2_sq)
  · have : Group.IsSolvable Klein := isSolvable_semidirect
    have : Group.IsSolvable KleinProd := inferInstance
    have : Group.IsSolvable H2 := isSolvable_semidirect
    exact isSolvable_semidirect
  · exact ⟨witness, witness_not_mem, 2, by norm_num, witness_sq_mem⟩


end MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted
