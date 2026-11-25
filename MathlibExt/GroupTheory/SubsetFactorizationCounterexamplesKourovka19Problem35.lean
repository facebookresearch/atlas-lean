/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.AddAut
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Subset factorizations of finite groups

We prove the counterexamples to subset factorization of every length at least three
from McCulloch's answer to Kourovka Notebook Problem 19.35.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35Wanted

/-- **Factorization of a group into subsets of given sizes.** Let $G$ be a group, $k$ a natural
number and $a_0, \dots, a_{k-1}$ natural numbers. The group $G$ has a subset factorization of
type $(a_0, \dots, a_{k-1})$ when there are finite subsets $A_0, \dots, A_{k-1}$ of $G$ with
$|A_i| = a_i$ for every $i$ such that $G = A_0 A_1 \cdots A_{k-1}$, that is, every $g \in G$ can be
written as $g = x_0 x_1 \cdots x_{k-1}$ with $x_i \in A_i$ for every $i$. -/
def HasSubsetFactorization (G : Type) [Group G] (k : ℕ) (a : Fin k → ℕ) : Prop :=
  ∃ A : Fin k → Finset G, (∀ i, (A i).card = a i) ∧
    ∀ g : G, ∃ x : Fin k → G, (∀ i, x i ∈ A i) ∧ (List.ofFn x).prod = g

/-- **Kourovka Problem 19.35: counterexamples to subset factorization of every length.** The
statement that for every natural number $k \ge 3$ there are a finite group $G$ and natural numbers
$a_0, \dots, a_{k-1}$, each at least $2$, with $a_0 a_1 \cdots a_{k-1} = |G|$, such that $G$ has
no subset factorization of type $(a_0, \dots, a_{k-1})$: there are no subsets
$A_0, \dots, A_{k-1}$ of $G$ with $|A_i| = a_i$ for every $i$ and $G = A_0 A_1 \cdots A_{k-1}$. -/
def subsetFactorizationCounterexampleEveryLength : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : Fin k → ℕ),
    (∀ i, 2 ≤ a i) ∧ ∏ i, a i = Nat.card G ∧ ¬ HasSubsetFactorization G k a

private theorem endpoints_of_factorization {G : Type} [Group G] [Finite G] {n : ℕ}
    {a : Fin (n + 2) → ℕ} (hfirst : a 0 = 2) (hlast : a (Fin.last (n + 1)) = 2)
    (hcard : ∏ i, a i = Nat.card G) (h : HasSubsetFactorization G (n + 2) a) :
    ∃ (a₀ b₀ : G) (M : Type) (f : M → G), a₀ ≠ 1 ∧ b₀ ≠ 1 ∧
      Function.Bijective (fun p : Bool × (M × Bool) =>
        (if p.1 then a₀ else 1) * f p.2.1 * (if p.2.2 then b₀ else 1)) := by
  classical
  obtain ⟨A, hA, hcover⟩ := h
  let product (x : ∀ i, (A i : Type)) : G := (List.ofFn fun i => (x i : G)).prod
  let := Fintype.ofFinite G
  have hP : Function.Bijective product := by
    refine (Fintype.bijective_iff_surjective_and_card product).2 ⟨?_, ?_⟩
    · intro g
      obtain ⟨x, hx, hprod⟩ := hcover g
      exact ⟨fun i => ⟨x i, hx i⟩, hprod⟩
    · simpa only [Fintype.card_pi, Fintype.card_coe, hA, Nat.card_eq_fintype_card] using hcard
  let l : Bool ≃ (A 0 : Type) := Fintype.equivOfCardEq (by simp [hA, hfirst])
  let r : Bool ≃ (A (Fin.last (n + 1)) : Type) :=
    Fintype.equivOfCardEq (by simp [hA, hlast])
  let M := ∀ i : Fin n, (A i.castSucc.succ : Type)
  let e : Bool × (M × Bool) ≃ ∀ i, (A i : Type) :=
    (l.prodCongr (((Equiv.refl M).prodCongr r).trans
      ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun i => (A i.succ : Type))))).trans
      (Fin.consEquiv fun i => (A i : Type))
  let a₀ : G := (l false : G)⁻¹ * (l true : G)
  let b₀ : G := (r true : G) * (r false : G)⁻¹
  let f (x : M) : G := (List.ofFn fun i => (x i : G)).prod
  refine ⟨a₀, b₀, M, f, ?_, ?_, ?_⟩
  · intro h
    exact Bool.false_ne_true (l.injective (Subtype.ext (inv_mul_eq_one.mp h)))
  · intro h
    exact Bool.false_ne_true (r.injective (Subtype.ext (mul_inv_eq_one.mp h).symm))
  -- Translate the first and last factors so that both contain the identity.
  let normalize : G ≃ G := (Equiv.mulLeft (l false : G)⁻¹).trans
    (Equiv.mulRight (r false : G)⁻¹)
  have heval (p : Bool × (M × Bool)) :
      product (e p) = (l p.1 : G) * f p.2.1 * (r p.2.2 : G) := by
    simp only [product, List.ofFn_succ (n := n + 1), List.prod_cons]
    rw [List.ofFn_succ', List.prod_concat]
    simp [e, f, Fin.consEquiv, Fin.snocEquiv, mul_assoc]
  have heq : normalize ∘ product ∘ e = fun p : Bool × (M × Bool) =>
      (if p.1 then a₀ else 1) * f p.2.1 * (if p.2.2 then b₀ else 1) := by
    funext p
    rcases p with ⟨i, x, j⟩
    cases i <;> cases j <;> simp [heval, normalize, a₀, b₀, ← mul_assoc]
  rw [← heq]
  exact normalize.bijective.comp (hP.comp e.bijective)

-- If multiplication moves every tuple with a false end choice to the corresponding
-- tuple with a true choice, it swaps the two classes and cannot have odd period.
private theorem pow_ne_one_of_two_choices {H X M : Type*} [Group H] [MulAction H X]
    [Nonempty X] {f : Bool × M → X} (hf : Function.Bijective f) {a : H}
    (ha : ∀ x, a • f (false, x) = f (true, x)) {n : ℕ} (hn : Odd n) : a ^ n ≠ 1 := by
  let e := Equiv.ofBijective f hf
  let side (x : X) : Bool := (e.symm x).1
  have hside (b : Bool) (x : M) : side (f (b, x)) = b := by
    change (e.symm (e (b, x))).1 = b
    rw [e.symm_apply_apply]
  have hswap (x : X) : side (a • x) = !(side x) := by
    obtain ⟨⟨b, y⟩, rfl⟩ := hf.2 x
    cases b
    · simp [ha, hside]
    · obtain ⟨⟨c, z⟩, hz⟩ := hf.2 (a • f (true, y))
      rw [← hz, hside, hside]
      cases c
      · rfl
      · rw [← ha] at hz
        exact (Bool.false_ne_true (congrArg Prod.fst (hf.1 (smul_left_cancel a hz)))).elim
  obtain ⟨m, rfl⟩ := hn
  have hpair (j : ℕ) : ∀ x : X, side ((a ^ (2 * j)) • x) = side x := by
    induction j with
    | zero => simp
    | succ j ih =>
      intro x
      rw [Nat.mul_succ, pow_add, mul_smul, ih, pow_two, mul_smul, hswap, hswap]
      simp
  intro h
  let x : X := Classical.choice ‹Nonempty X›
  have hx : side x = !(side x) := calc
    side x = side ((a ^ (2 * m + 1)) • x) := by rw [h, one_smul]
    _ = !(side x) := by rw [pow_succ, mul_smul, hpair, hswap]
  cases hcolor : side x <;> simp [hcolor] at hx

private abbrev affineAction (K : Type) [Field K] : Kˣ →* MulAut (Multiplicative K) :=
  (MulAutMultiplicative K).symm.toMonoidHom.comp AddAut.mulLeft

private abbrev AffineGroup (K : Type) [Field K] :=
  Multiplicative K ⋊[affineAction K] Kˣ

private theorem affine_mul_translation {K : Type} [Field K] (g h : AffineGroup K) :
    (g * h).left.toAdd = g.left.toAdd + (g.right : K) * h.left.toAdd := rfl

-- An affine map with nontrivial multiplier is conjugate to its linear part by
-- translation to its fixed point.
private theorem affine_pow_card_units {K : Type} [Field K] (g : AffineGroup K)
    (hg : g.right ≠ 1) : g ^ Nat.card Kˣ = 1 := by
  have hu : (1 - (g.right : K)) ≠ 0 := by
    exact sub_ne_zero.mpr fun h => hg (Units.ext h.symm)
  let t : K := g.left.toAdd / (1 - (g.right : K))
  let v : AffineGroup K := SemidirectProduct.inl (Multiplicative.ofAdd t)
  let u : AffineGroup K := SemidirectProduct.inr g.right
  have ht : t * (1 - (g.right : K)) = g.left.toAdd := div_mul_cancel₀ _ hu
  have hconj : g * v = v * u := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      rw [affine_mul_translation, affine_mul_translation]
      change g.left.toAdd + (g.right : K) * t = t + 1 * 0
      rw [← ht, mul_sub, mul_one, one_mul, add_zero, mul_comm t, sub_add_cancel]
    · simp [v, u]
  have hg' : g = MulAut.conj v u := by
    rw [MulAut.conj_apply, ← hconj, mul_inv_cancel_right]
  have hu' : u ^ Nat.card Kˣ = 1 := by
    dsimp [u]
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [hg', ← map_pow, hu', map_one]

private theorem no_bijective_endpoint_product {K : Type} [Field K] {M : Type}
    (hodd : Odd (Nat.card Kˣ)) {a b : AffineGroup K} (ha : a ≠ 1) (hb : b ≠ 1)
    (f : M → AffineGroup K) :
    ¬ Function.Bijective (fun p : Bool × (M × Bool) =>
      (if p.1 then a else 1) * f p.2.1 * (if p.2.2 then b else 1)) := by
  intro h
  have ha₁ : a.right = 1 := by
    by_contra ha₁
    have hn := pow_ne_one_of_two_choices h (a := a) (by simp [mul_assoc]) hodd
    exact hn (affine_pow_card_units a ha₁)
  have hb₁ : b.right = 1 := by
    by_contra hb₁
    let swapEnds : Bool × (M × Bool) ≃ Bool × (M × Bool) :=
      { toFun := fun p => (p.2.2, p.2.1, p.1)
        invFun := fun p => (p.2.2, p.2.1, p.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hn := pow_ne_one_of_two_choices (h.comp swapEnds.bijective) (a := MulOpposite.op b)
      (by intro p; simp [swapEnds]) hodd
    exact hn (by rw [← MulOpposite.op_pow, affine_pow_card_units b hb₁]; rfl)
  have nonzero_translation (g : AffineGroup K) (hg : g ≠ 1) (hg₁ : g.right = 1) :
      g.left.toAdd ≠ 0 := fun hzero => hg (SemidirectProduct.ext hzero hg₁)
  -- A middle product with this multiplier sends the last translation to the first.
  let c : Kˣ := Units.mk0 (a.left.toAdd / b.left.toAdd)
    (div_ne_zero (nonzero_translation a ha ha₁) (nonzero_translation b hb hb₁))
  obtain ⟨⟨i, x, j⟩, hx⟩ := h.2 (SemidirectProduct.inr c)
  have hx₁ : (f x).right = c := by
    have hc := congrArg SemidirectProduct.right hx
    cases i <;> cases j <;> simpa [ha₁, hb₁] using hc
  have hcollision : a * f x = f x * b := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      rw [affine_mul_translation, affine_mul_translation, ha₁, hx₁, Units.val_one, one_mul,
        add_comm a.left.toAdd]
      congr 1
      exact (div_mul_cancel₀ _ (nonzero_translation b hb hb₁)).symm
    · simp [ha₁, hb₁]
  have he := h.1 (a₁ := (true, x, false)) (a₂ := (false, x, true)) (by simpa using hcollision)
  exact Bool.false_ne_true (congrArg Prod.fst he.symm)

/--
**Finite groups without subset factorizations exist for every length.** For every natural number
$k \ge 3$ there are a finite group $G$ and natural numbers $a_0, \dots, a_{k-1}$, each at least
$2$, with $a_0 a_1 \cdots a_{k-1} = |G|$, such that there are no subsets $A_0, \dots, A_{k-1}$ of
$G$ with $|A_i| = a_i$ for every $i$ and $G = A_0 A_1 \cdots A_{k-1}$, that is, with every element
of $G$ a product $x_0 x_1 \cdots x_{k-1}$ where $x_i \in A_i$ for every $i$.

In McCulloch's Theorem 2.3, $G$ is a Frobenius group of order $2^{k-1}(2^{k-1} - 1)$ and the
factors are $(2, \dots, 2, 2^{k-1} - 1, 2)$; the case $k = 3$ is Bergman's example in the
alternating group $A_4$. This answers Kourovka Problem 19.35 (M. H. Hooshmand) in the negative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 19.35 (M. H. Hooshmand); resolution: R. McCulloch, Some answers regarding factorizations of
finite groups, arXiv:2607.20569 (2026); counterexamples first given by M. Kabenyuk, Factorizations
of finite groups, arXiv:2102.08605, Kourovka Archive, Problem 19.35: No (Bergman's A4 example for k
= 3); counterexamples for all k ≥ 3 are constructed in (McCulloch); paper, Theorem 2.3: the
Frobenius group of order 2^(k-1)(2^(k-1) - 1) has no k-fold factorization for (2, …, 2, 2^(k-1) - 1,
2), https://arxiv.org/abs/2607.20569.
-/
theorem subsetFactorizationCounterexampleEveryLength_holds :
    subsetFactorizationCounterexampleEveryLength := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 3 := ⟨k - 3, by omega⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (n + 2)
  let : Finite (AffineGroup K) :=
    Finite.of_equiv (Multiplicative K × Kˣ) SemidirectProduct.equivProd.symm
  have hK : Nat.card K = 2 ^ (n + 2) := GaloisField.card 2 (n + 2) (by omega)
  let a : Fin (n + 3) → ℕ :=
    Fin.snoc (Fin.snoc (fun _ : Fin (n + 1) => 2) (2 ^ (n + 2) - 1)) 2
  have hq : 4 ≤ (2 : ℕ) ^ (n + 2) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n + 2)
  have hcard : ∏ i, a i = Nat.card (AffineGroup K) := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, SemidirectProduct.card, Nat.card_units,
      show Nat.card (Multiplicative K) = Nat.card K from rfl, hK]
    simp only [a, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [mul_right_comm, ← pow_succ]
  refine ⟨AffineGroup K, inferInstance, inferInstance, a, ?_, hcard, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [a]
    · simp only [a, Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [Fin.snoc_last]
        omega
      · simp
  · intro h
    have hodd : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units, hK, pow_succ]
      refine ⟨2 ^ (n + 1) - 1, ?_⟩
      have : 0 < (2 : ℕ) ^ (n + 1) := by positivity
      omega
    obtain ⟨a₀, b₀, M, f, ha, hb, hbij⟩ :=
      endpoints_of_factorization (n := n + 1) (by simp [a])
        (by simp [a]) hcard h
    exact no_bijective_endpoint_product hodd ha hb f hbij

end MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35Wanted
