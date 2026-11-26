/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Lev's rectification principle

Every sufficiently small subset of a group of prime order admits a Freiman isomorphism
of the prescribed order to a set of integers (`exists_freimanIso_to_int`).

A relation between two sums of `ℓ` terms gives a row that is a sum of `ℓ` differences
of coordinate vectors. Complete a maximal independent family of these rows to a square
matrix by adjoining coordinate rows. With `k` relation rows, multilinearity bounds the
absolute determinant by `ℓ ^ k`. The cardinality hypothesis makes this strictly less than
the modulus. Cramer's rule then gives integer labels satisfying every relation and reducing
modulo the prime to a common nonzero multiple of the original labels.
-/

public section

namespace MathlibExt.Combinatorics.ValidOrderingWanted

open Matrix
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Deleting columns of a coordinate vector leaves either a coordinate vector or zero. -/
private def IsVertex (v : ι → ℤ) : Prop :=
  v = 0 ∨ ∃ i, v = Pi.single i 1

private lemma IsVertex.restrict {κ : Type*} [DecidableEq κ] {v : ι → ℤ}
    (hv : IsVertex v) {g : κ → ι} (hg : Function.Injective g) : IsVertex (v ∘ g) := by
  rcases hv with rfl | ⟨i, rfl⟩
  · exact Or.inl rfl
  · by_cases hi : ∃ j, g j = i
    · obtain ⟨j, rfl⟩ := hi
      exact Or.inr ⟨j, funext fun k => by simp [Function.comp, Pi.single_apply, hg.eq_iff]⟩
    · push Not at hi
      exact Or.inl (funext fun k => by simp [Function.comp, hi])

/-- Every square minor of an oriented incidence matrix has absolute value at most one. -/
private lemma abs_det_edges_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i, ∃ v w, IsVertex v ∧ IsVertex w ∧ M i = v - w) : |M.det| ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hz : ∀ i, ∑ j, M i j = 0
    · have hker : M *ᵥ (fun _ => 1 : Fin (n + 1) → ℤ) = 0 := by
        ext i
        simpa [mulVec, dotProduct] using hz i
      rw [det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
        (i := 0) (by exact one_mem _)]
      simp
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hz
      have hs : ∃ j c, |c| = 1 ∧ M i = Pi.single j c := by
        obtain ⟨v, w, hv, hw, hr⟩ := h i
        rcases hv with rfl | ⟨a, rfl⟩ <;> rcases hw with rfl | ⟨b, rfl⟩
        · simp [hr] at hi
        · exact ⟨b, -1, by decide, by simp [hr, ← Pi.single_neg]⟩
        · exact ⟨a, 1, rfl, by simp [hr]⟩
        · simp [hr, Finset.sum_sub_distrib, Pi.single_apply] at hi
      obtain ⟨j, c, hc, hr⟩ := hs
      rw [det_succ_row M i, Fintype.sum_eq_single j]
      · rw [hr, Pi.single_eq_same, abs_mul, abs_mul, abs_pow]
        simp only [abs_neg, abs_one, one_pow, one_mul, hc]
        apply ih
        intro k
        obtain ⟨v, w, hv, hw, he⟩ := h (i.succAbove k)
        exact ⟨v ∘ j.succAbove, w ∘ j.succAbove, hv.restrict Fin.succAbove_right_injective,
          hw.restrict Fin.succAbove_right_injective, congrArg (· ∘ j.succAbove) he⟩
      · intro k hk
        simp [hr, Pi.single_eq_of_ne hk]

private lemma abs_det_edges [Fintype ι] (M : Matrix ι ι ℤ)
    (h : ∀ i, ∃ v w, IsVertex v ∧ IsVertex w ∧ M i = v - w) : |M.det| ≤ 1 := by
  let e := (Fintype.equivFin ι).symm
  rw [← M.det_submatrix_equiv_self e]
  apply abs_det_edges_fin
  intro i
  obtain ⟨v, w, hv, hw, hr⟩ := h (e i)
  exact ⟨v ∘ e, w ∘ e, hv.restrict e.injective, hw.restrict e.injective, congrArg (· ∘ e) hr⟩

/-- A determinant with a sum of edges in each row is bounded by the product of the
numbers of edges. Each term of the multilinear expansion is an incidence determinant. -/
private lemma abs_det_sum_edges [Fintype ι] (d : ι → ℕ) (g : (i : ι) → Fin (d i) → ι → ℤ)
    (hg : ∀ i k, ∃ v w, IsVertex v ∧ IsVertex w ∧ g i k = v - w) :
    |(Matrix.of fun i => ∑ k, g i k).det| ≤ (∏ i, d i : ℕ) := by
  classical
  have hexpand : (Matrix.of fun i => ∑ k, g i k).det =
      ∑ r : (i : ι) → Fin (d i), (Matrix.of fun i => g i (r i)).det :=
    detRowAlternating.toMultilinearMap.map_sum g
  rw [hexpand]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : (i : ι) → Fin (d i), (1 : ℤ) :=
      Finset.sum_le_sum fun r _ => abs_det_edges _ fun i => hg i (r i)
    _ = _ := by simp [Fintype.card_pi]

private def relationRow {ℓ : ℕ} (a b : Fin ℓ → ι) : ι → ℤ :=
  ∑ k, (Pi.single (a k) 1 - Pi.single (b k) 1)

private lemma relationRow_dotProduct [Fintype ι] {ℓ : ℕ} (a b : Fin ℓ → ι) (z : ι → ℤ) :
    relationRow a b ⬝ᵥ z = (∑ k, z (a k)) - ∑ k, z (b k) := by
  simp [relationRow, sum_dotProduct, sub_dotProduct, single_dotProduct, Finset.sum_sub_distrib]

private def IsRelation {p : ℕ} (ℓ : ℕ) (x : ι → ZMod p) (r : ι → ℤ) : Prop :=
  ∃ a b : Fin ℓ → ι, r = relationRow a b ∧ (∑ k, x (a k)) = ∑ k, x (b k)

/-- Choose as many relation rows as possible in a nonsingular matrix completed by rows
of the identity. Any relation substituted for a remaining coordinate row kills the determinant. -/
private lemma exists_relation_matrix [Fintype ι] (R : (ι → ℤ) → Prop) :
    ∃ (s : Finset ι) (M : Matrix ι ι ℤ), M.det ≠ 0 ∧
      (∀ i ∈ s, R (M i)) ∧ (∀ i ∉ s, M i = Pi.single i 1) ∧
      ∀ i ∉ s, ∀ r, R r → (M.updateRow i r).det = 0 := by
  classical
  let good (s : Finset ι) := ∃ M : Matrix ι ι ℤ, M.det ≠ 0 ∧
    (∀ i ∈ s, R (M i)) ∧ ∀ i ∉ s, M i = Pi.single i 1
  have hempty : good ∅ := ⟨1, by simp, by simp, fun _ _ => funext fun _ => Matrix.one_eq_pi_single⟩
  obtain ⟨s, -, hs⟩ := Finite.exists_le_maximal hempty
  obtain ⟨M, hd, hin, hout⟩ := hs.prop
  refine ⟨s, M, hd, hin, hout, ?_⟩
  intro i hi r hr
  by_contra hdet
  have hgood : good (insert i s) := by
    refine ⟨M.updateRow i r, hdet, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hr
      · simpa [Matrix.updateRow_ne (ne_of_mem_of_not_mem hj hi)] using hin j hj
    · intro j hj
      simp only [Finset.mem_insert, not_or] at hj
      simpa [Matrix.updateRow_ne hj.1] using hout j hj.2
  exact hi (hs.le_of_ge hgood (Finset.subset_insert i s) (Finset.mem_insert_self ..))

private lemma abs_det_relation_matrix [Fintype ι] {ℓ p : ℕ} {x : ι → ZMod p}
    {s : Finset ι} {M : Matrix ι ι ℤ} (hin : ∀ i ∈ s, IsRelation ℓ x (M i))
    (hout : ∀ i ∉ s, M i = Pi.single i 1) : |M.det| ≤ (ℓ ^ s.card : ℕ) := by
  classical
  let d (i : ι) := if i ∈ s then ℓ else 1
  let decomposes (i : ι) (m : ℕ) := ∃ g : Fin m → ι → ℤ, M i = ∑ k, g k ∧
      ∀ k, ∃ v w, IsVertex v ∧ IsVertex w ∧ g k = v - w
  have hrow (i : ι) : decomposes i (d i) := by
    by_cases hi : i ∈ s
    · obtain ⟨a, b, hr, -⟩ := hin i hi
      rw [show d i = ℓ by simp [d, hi]]
      exact ⟨fun k => Pi.single (a k) 1 - Pi.single (b k) 1, hr,
        fun k => ⟨_, _, Or.inr ⟨a k, rfl⟩, Or.inr ⟨b k, rfl⟩, rfl⟩⟩
    · rw [show d i = 1 by simp [d, hi]]
      exact ⟨fun _ => Pi.single i 1, by simp [hout i hi],
        fun _ => ⟨_, 0, Or.inr ⟨i, rfl⟩, Or.inl rfl, (sub_zero _).symm⟩⟩
  choose g hM hg using hrow
  have heq : M = Matrix.of fun i => ∑ k, g i k := funext hM
  rw [heq]
  simpa [d, Finset.prod_ite] using abs_det_sum_edges d g hg

/-- The cardinality hypothesis makes every nonzero relation determinant a unit modulo the
prime. At least one row must be a coordinate row, since all relation rows sum to zero. -/
private lemma det_ne_zero_mod [Fintype ι] [Nonempty ι] {ℓ p : ℕ} (hℓ : 2 ≤ ℓ) (hp : p.Prime)
    (hcard : Fintype.card ι ≤ ⌈Real.log p / Real.log ℓ⌉₊) {x : ι → ZMod p}
    {s : Finset ι} {M : Matrix ι ι ℤ} (hd : M.det ≠ 0) (hin : ∀ i ∈ s, IsRelation ℓ x (M i))
    (hout : ∀ i ∉ s, M i = Pi.single i 1) : (M.det : ZMod p) ≠ 0 := by
  have hs : s.card < Fintype.card ι := by
    apply (Finset.card_lt_iff_ne_univ s).mpr
    rintro rfl
    apply hd
    apply det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := fun _ => (1 : ℤ))
      (i := Classical.arbitrary ι) _ (one_mem _)
    funext i
    obtain ⟨a, b, hr, -⟩ := hin i (Finset.mem_univ i)
    simp [mulVec, hr, relationRow_dotProduct]
  have hlog := Nat.lt_ceil.mp (hs.trans_le hcard)
  have hpos : 1 < (ℓ : ℝ) := by exact_mod_cast (show 1 < ℓ by omega)
  have hlt : (ℓ : ℝ) ^ s.card < p := by
    apply (Real.log_lt_log_iff (by positivity) (by exact_mod_cast hp.pos)).mp
    rw [Real.log_pow]
    exact (lt_div_iff₀ (Real.log_pos hpos)).mp hlog
  have hpow : ℓ ^ s.card < p := by exact_mod_cast hlt
  intro h
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) (Int.natAbs_dvd_natAbs.mpr hdiv)
  have hbound := abs_det_relation_matrix hin hout
  rw [← Int.natCast_natAbs] at hbound
  exact (not_le_of_gt hpow) (hle.trans (by exact_mod_cast hbound))

/-- Lift the residue labels up to a common nonzero multiplier. Cramer's rule with zero
right-hand sides on the relation rows enforces every relation over the integers. -/
private lemma lift_relations [Fintype ι] [Nonempty ι] {ℓ p : ℕ} (hℓ : 2 ≤ ℓ) (hp : p.Prime)
    (hcard : Fintype.card ι ≤ ⌈Real.log p / Real.log ℓ⌉₊) (x : ι → ZMod p) :
    ∃ (y : ι → ℤ) (c : ZMod p), c ≠ 0 ∧ (∀ i, (y i : ZMod p) = c * x i) ∧
      ∀ r, IsRelation ℓ x r → r ⬝ᵥ y = 0 := by
  classical
  obtain ⟨s, M, hd, hin, hout, hmax⟩ := exists_relation_matrix (IsRelation ℓ x)
  choose z hz using fun i => ZMod.intCast_surjective (x i)
  let b (i : ι) : ℤ := if i ∈ s then 0 else z i
  refine ⟨M.adjugate *ᵥ b, M.det, det_ne_zero_mod hℓ hp hcard hd hin hout, ?_, ?_⟩
  · have hb (i : ι) : (b i : ZMod p) = ((M *ᵥ z) i : ℤ) := by
      by_cases hi : i ∈ s
      · obtain ⟨u, v, hr, he⟩ := hin i hi
        simp [b, hi, mulVec, hr, relationRow_dotProduct, hz, he]
      · simp [b, hi, mulVec, hout i hi, single_dotProduct]
    intro i
    have heq : ((M.adjugate *ᵥ b) i : ZMod p) =
        ((M.adjugate *ᵥ (M *ᵥ z)) i : ℤ) := by
      simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hb]
    simpa [mulVec_mulVec, adjugate_mul, smul_mulVec, hz] using heq
  · intro r hr
    rw [dotProduct_mulVec, ← mulVec_transpose, adjugate_transpose, ← cramer_eq_adjugate_mulVec]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · simp [b, hi]
    · rw [cramer_transpose_apply, hmax i hi r hr, zero_mul]

/-- Enumerate the terms of a multiset by a tuple with values in its prescribed support. -/
private lemma exists_tuple {α : Type*} {A : Finset α} {ℓ : ℕ} (s : Multiset α)
    (hA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (hℓ : s.card = ℓ) :
    ∃ a : Fin ℓ → A, s = ↑(List.ofFn fun k => (a k : α)) := by
  have hex : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  obtain ⟨n, g, rfl⟩ := List.exists_iff_exists_tuple.mp hex
  simp only [Multiset.coe_card, List.length_ofFn] at hℓ
  subst ℓ
  exact ⟨fun k => ⟨g k, hA (by simp)⟩, rfl⟩

/-- **Lev's rectification principle.** Let $\ell \ge 2$ be a natural number, $p$ a prime and
$A$ a subset of $\mathbb{Z}/p\mathbb{Z}$ with $|A| \le \lceil \log p / \log \ell \rceil$. Then
there are a finite set $B$ of integers and a map $f \colon \mathbb{Z}/p\mathbb{Z} \to \mathbb{Z}$
that is a Freiman isomorphism of order $\ell$ from $A$ to $B$: $f$ maps $A$ bijectively onto
$B$, and for all $a_1, \dots, a_\ell, b_1, \dots, b_\ell \in A$ we have
$f(a_1) + \cdots + f(a_\ell) = f(b_1) + \cdots + f(b_\ell)$ if and only if
$a_1 + \cdots + a_\ell = b_1 + \cdots + b_\ell$.

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 3. -/
theorem exists_freimanIso_to_int (ℓ p : ℕ)
    (hℓ : 2 ≤ ℓ) (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.card ≤ ⌈Real.log p / Real.log ℓ⌉₊) :
    ∃ (B : Finset ℤ) (f : ZMod p → ℤ),
      IsAddFreimanIso ℓ (A : Set (ZMod p)) (B : Set ℤ) f := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rcases A.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, fun _ => 0, ?_⟩
    simp only [Finset.coe_empty]
    exact isAddFreimanIso_empty
  have : Nonempty A := hne.to_subtype
  obtain ⟨y, c, hc, hy, hrels⟩ :=
    lift_relations hℓ hp (by simpa using hA) (fun i : A => (i : ZMod p))
  let f (x : ZMod p) : ℤ := if hx : x ∈ A then y ⟨x, hx⟩ else 0
  have hf (i : A) : f i = y i := by simp [f]
  refine ⟨A.image f, f, ?_, ?_⟩
  · rw [Finset.coe_image]
    apply Set.InjOn.bijOn_image
    intro x hx x' hx' he
    have he' : y ⟨x, hx⟩ = y ⟨x', hx'⟩ :=
      (hf ⟨x, hx⟩).symm.trans (he.trans (hf ⟨x', hx'⟩))
    apply mul_left_cancel₀ hc
    simpa only [hy] using congrArg ((↑) : ℤ → ZMod p) he'
  · intro s t hsA htA hs ht
    obtain ⟨a, rfl⟩ := exists_tuple s hsA hs
    obtain ⟨b, rfl⟩ := exists_tuple t htA ht
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply, hf]
    constructor
    · intro he
      apply mul_left_cancel₀ hc
      simpa only [Finset.mul_sum, ← hy, ← Int.cast_sum] using congrArg ((↑) : ℤ → ZMod p) he
    · intro he
      exact sub_eq_zero.mp (relationRow_dotProduct a b y ▸ hrels _ ⟨a, b, rfl, he⟩)

end MathlibExt.Combinatorics.ValidOrderingWanted
