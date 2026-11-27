/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RealRooted
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Order.Sublattice
import Mathlib.Tactic.Ring

/-!
# A distributive lattice with a non-real-rooted chain polynomial

Stembridge's counterexample to Stanley's Problem 20' is a finite sublattice of a product
of two chains. We compute its chain polynomial one rectangle at a time and certify that
the modulus decreases on moving vertically away from the real axis.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DistributiveLatticeChainPolynomialAMR156Problem0021Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 20' (chain polynomial of a finite distributive lattice). UnsolvedMath record UM-00801195
(`AMR-156-0021`), dataset ulamai/UnsolvedMath v1.8.0.

A finite distributive lattice is a type with `DistribLattice` and `Fintype` instances; chains are
finite subsets totally ordered by `≤` (the empty chain gives `c_0 = 1`). `C(L, t)` is nonzero, so
real-rootedness is `Polynomial.IsRealRooted` (MathlibExt) of its image in `ℂ[t]`. The (empty)
lattice on an empty type has `C = 1` and is harmless.
-/

open Classical in
/-- **Chain polynomial.** For a finite partially ordered set $P$ and each natural number $k$, let
$c_k(P)$ be the number of $k$-element chains of $P$, that is, of $k$-element subsets of $P$ any two
of whose elements are comparable; in particular $c_0(P) = 1$, counting the empty chain. The chain
polynomial of $P$ is the polynomial $C(P, t) = \sum_{k \ge 0} c_k(P)\, t^k$ with integer
coefficients. -/
noncomputable def chainPolynomial (L : Type*) [PartialOrder L] [Fintype L] : Polynomial ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset L)).filter (fun s : Finset L => IsChain (· ≤ ·) (s : Set L)),
    Polynomial.X ^ s.card

/-- **Stanley's Problem 20' on chain polynomials of distributive lattices.** The proposition that
for every finite distributive lattice $L$, every complex root of the chain polynomial $C(L, t)$ is
real, where $C(L, t) = \sum_{k \ge 0} c_k(L)\, t^k$ and $c_k(L)$ is the number of $k$-element
chains of $L$. -/
def distributiveLatticeChainPolynomialRealRooted : Prop :=
  ∀ (L : Type) [DistribLattice L] [Fintype L],
    ((chainPolynomial L).map (Int.castRingHom ℂ)).IsRealRooted

open Polynomial Finset

private noncomputable def chains {L : Type*} [PartialOrder L] (s : Finset L) :
    Finset (Finset L) := by
  classical
  exact s.powerset.filter fun t => IsChain (· ≤ ·) (t : Set L)

private lemma mem_chains {L : Type*} [PartialOrder L] {s t : Finset L} :
    t ∈ chains s ↔ t ⊆ s ∧ IsChain (· ≤ ·) (t : Set L) := by
  classical
  simp [chains]

private noncomputable def weight {L : Type*} [PartialOrder L] (s : Finset L) : Polynomial ℤ :=
  ∑ t ∈ chains s, X ^ t.card

private lemma weight_insert_top {L : Type*} [PartialOrder L] [DecidableEq L]
    (s : Finset L) (a : L) (ha : a ∉ s) (ht : ∀ b ∈ s, b ≤ a) :
    weight (insert a s) = (1 + X) * weight s := by
  classical
  unfold weight chains
  rw [sum_filter, sum_filter, sum_powerset_insert ha, add_mul, one_mul, mul_sum]
  congr 1
  apply sum_congr rfl
  intro t ht'
  have hts := mem_powerset.mp ht'
  have ha' : a ∉ t := fun h => ha (hts h)
  have hiff : IsChain (· ≤ ·) (insert a (t : Set L)) ↔ IsChain (· ≤ ·) (t : Set L) := by
    refine ⟨IsChain.mono (by simp), fun h => ?_⟩
    exact h.insert fun b hb _ => Or.inr (ht b (hts hb))
  by_cases h : IsChain (· ≤ ·) (t : Set L) <;>
    simp [hiff, h, card_insert_of_notMem ha', pow_succ, mul_comm]

-- The lattice points between the two boundaries of the skew shape 888888765/76654321
-- of Alexandersson and Jal, arXiv:2410.00127v1, Figure 20 and Corollary 5.12.
private def present (i j : ℕ) : Prop :=
  i < 10 ∧ j < 9 ∧ j ≤ i + 5 ∧ i ≤ j + 1 + (if 8 ≤ i then 1 else 0)

private instance decPresent (i j : ℕ) : Decidable (present i j) := by
  unfold present
  infer_instance

private def board : Sublattice (Fin 10 × Fin 9) where
  carrier := {p | present p.1 p.2}
  supClosed' := by
    rintro ⟨i, j⟩ hp ⟨k, l⟩ hq
    change present (max i.val k.val) (max j.val l.val)
    change present i.val j.val at hp
    change present k.val l.val at hq
    unfold present at *
    split_ifs at * <;> omega
  infClosed' := by
    rintro ⟨i, j⟩ hp ⟨k, l⟩ hq
    change present (min i.val k.val) (min j.val l.val)
    change present i.val j.val at hp
    change present k.val l.val at hq
    unfold present at *
    split_ifs at * <;> omega

private abbrev Point := ↥board

private instance pointFintype : Fintype Point :=
  inferInstanceAs (Fintype {p : Fin 10 × Fin 9 // present p.1 p.2})

private def box (i j : ℕ) : Finset Point :=
  univ.filter fun p => p.val.1.val < i ∧ p.val.2.val < j

private lemma mem_box {p : Point} {i j : ℕ} :
    p ∈ box i j ↔ p.val.1.val < i ∧ p.val.2.val < j := by simp [box]

-- A chain avoiding the top-right corner must miss either its row or its column.
-- Points on those two edges are incomparable.
private lemma box_overlap (i j : ℕ) :
    weight (box i (j + 1) ∪ box (i + 1) j) =
      weight (box i (j + 1)) + weight (box (i + 1) j) - weight (box i j) := by
  classical
  let A := box i (j + 1)
  let B := box (i + 1) j
  have hu : chains (A ∪ B) = chains A ∪ chains B := by
    ext t
    simp only [mem_union, mem_chains]
    constructor
    · rintro ⟨ht, hc⟩
      by_cases hA : t ⊆ A
      · exact Or.inl ⟨hA, hc⟩
      right
      refine ⟨?_, hc⟩
      obtain ⟨p, hp, hpA⟩ := Finset.not_subset.mp hA
      have hpB := (mem_union.mp (ht hp)).resolve_left hpA
      intro q hq
      by_contra hqB
      have hqA := (mem_union.mp (ht hq)).resolve_right hqB
      simp only [A, B, mem_box] at hpA hpB hqA hqB
      rcases hc.total hp hq with h | h
      · have := h.1
        omega
      · have := h.2
        omega
    · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
      · exact ⟨h.trans subset_union_left, hc⟩
      · exact ⟨h.trans subset_union_right, hc⟩
  have hi : chains (box i j) = chains A ∩ chains B := by
    ext t
    simp only [mem_inter, mem_chains, Finset.subset_iff, A, B, mem_box]
    grind
  unfold weight
  change (∑ t ∈ chains (A ∪ B), _) = _
  rw [hu, hi, eq_sub_iff_add_eq]
  exact sum_union_inter

private lemma box_step (i j : ℕ) :
    weight (box (i + 1) (j + 1)) = (if present i j then 1 + X else 1) *
      (weight (box i (j + 1)) + weight (box (i + 1) j) - weight (box i j)) := by
  classical
  rw [← box_overlap]
  let s := box i (j + 1) ∪ box (i + 1) j
  by_cases h : present i j
  · let p : Point := ⟨(⟨i, h.1⟩, ⟨j, h.2.1⟩), h⟩
    have he : box (i + 1) (j + 1) = insert p s := by
      ext q
      simp only [mem_box, mem_insert, s, mem_union]
      have : q = p ↔ q.val.1.val = i ∧ q.val.2.val = j := by
        simp [p, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff]
      rw [this]
      omega
    simp only [h, ite_true]
    rw [he, weight_insert_top]
    · simp [s, mem_box, p]
    · intro q hq
      simp only [s, mem_union, mem_box] at hq
      change q.val.1.val ≤ i ∧ q.val.2.val ≤ j
      omega
  · have he : box (i + 1) (j + 1) = s := by
      ext q
      have hp : present q.val.1 q.val.2 := q.property
      simp only [s, mem_union, mem_box]
      have hne : ¬(q.val.1.val = i ∧ q.val.2.val = j) := by
        rintro ⟨rfl, rfl⟩
        exact h hp
      omega
    simp only [h, ite_false, one_mul, he]
    rfl

-- Little-endian coefficient lists implement the same recurrence with integer arithmetic.
private def addCoeffs : List ℤ → List ℤ → List ℤ :=
  List.zipWithAll fun a b => a.getD 0 + b.getD 0

private def subCoeffs : List ℤ → List ℤ → List ℤ :=
  List.zipWithAll fun a b => a.getD 0 - b.getD 0

private def nextRow (i : ℕ) (prev : ℕ → List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | j + 1 =>
    let base := subCoeffs (addCoeffs (prev (j + 1)) (nextRow i prev j)) (prev j)
    if present i j then addCoeffs base (0 :: base) else base

private def counts : ℕ → ℕ → List ℤ
  | 0 => fun _ => [1]
  | i + 1 => nextRow i (counts i)

private lemma weight_empty : weight (∅ : Finset Point) = 1 := by
  classical
  simp [weight, chains, sum_filter]

private lemma weight_eq_counts (i j : ℕ) : weight (box i j) = ofCoeffList (counts i j) := by
  induction i generalizing j with
  | zero => simp [box, counts, weight_empty, ofCoeffList_cons]
  | succ i ih =>
    induction j with
    | zero => simp [box, counts, nextRow, weight_empty, ofCoeffList_cons]
    | succ j hj =>
      rw [box_step, ih, ih, hj]
      change _ = ofCoeffList (nextRow i (counts i) (j + 1))
      rw [nextRow]
      by_cases h : present i j <;>
        simp [h, addCoeffs, subCoeffs, counts, add_mul]

private def coefficients : List ℤ :=
  [1, 50, 1033, 11964, 88974, 459410, 1730750, 4915950, 10758509, 18391458,
    24737837, 26221600, 21809676, 14077686, 6911684, 2495078, 624600, 96884, 7016]

private lemma board_polynomial : chainPolynomial Point = ofCoeffList coefficients := by
  classical
  have hbox : box 10 9 = univ := by ext p; simp [mem_box]
  have h := weight_eq_counts 10 9
  rw [hbox] at h
  have hc : counts 10 9 = coefficients := by decide +kernel
  simpa [hc, weight, chains, chainPolynomial] using h

-- In a product of real linear factors, each factor's distance from zero increases
-- (weakly) if we add an imaginary component to its argument.
private lemma normSq_eval_le (p : Polynomial ℂ) (h : p.IsRealRooted) (z : ℂ) :
    Complex.normSq (p.eval (z.re : ℂ)) ≤ Complex.normSq (p.eval z) := by
  simp only [(IsAlgClosed.splits p).eval_eq_prod_roots, map_mul, map_multiset_prod,
    Multiset.map_map, Function.comp_def]
  apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
  apply Multiset.prod_map_le_prod_map₀
  · exact fun _ _ => Complex.normSq_nonneg _
  · intro w hw
    simp [Complex.normSq_apply, h w hw, sq_nonneg, ← sq]

private def horner (a b : ℚ) : List ℤ → ℚ × ℚ
  | [] => (0, 0)
  | c :: cs =>
    let (u, v) := horner a b cs
    (c + a * u - b * v, a * v + b * u)

private lemma eval_horner (a b : ℚ) (cs : List ℤ) :
    ((ofCoeffList cs).map (Int.castRingHom ℂ)).eval ⟨a, b⟩ =
      ⟨(horner a b cs).1, (horner a b cs).2⟩ := by
  induction cs with
  | nil => simp [horner, Complex.ext_iff]
  | cons c cs ih =>
    simp only [ofCoeffList_cons, Polynomial.map_add, map_C, Int.coe_castRingHom,
      Polynomial.map_mul, map_X, eval_add, eval_C, eval_mul, eval_X, ih]
    apply Complex.ext <;> simp [horner, Complex.mul_re, Complex.mul_im]
    ring

private def evalNormSq (a b : ℚ) : ℚ :=
  let (u, v) := horner a b coefficients
  u * u + v * v

private lemma evalNormSq_spec (a b : ℚ) :
    Complex.normSq (((chainPolynomial Point).map (Int.castRingHom ℂ)).eval ⟨a, b⟩) =
      (evalNormSq a b : ℝ) := by
  rw [board_polynomial, eval_horner]
  simp [Complex.normSq_apply, evalNormSq]

/--
**Stanley's Problem 20' has a negative answer.** It is not true that for every finite
distributive lattice $L$ every complex root of the chain polynomial $C(L, t)$ is real, where
$C(L, t) = \sum_{k \ge 0} c_k(L)\, t^k$ and $c_k(L)$ is the number of $k$-element chains of $L$.

For a finite poset $P$ let $J(P)$ be the distributive lattice of its order ideals, and for a
naturally labeled $P$ let $W(P, x) = \sum_{\sigma} x^{\operatorname{des}(\sigma)}$, the sum over
the linear extensions $\sigma$ of $P$, where $\operatorname{des}(\sigma)$ is the number of descents
of $\sigma$. For naturally labeled $P$, real-rootedness of $C(J(P), t)$ is equivalent to that of
$W(P, x)$ (Stanley's text before Problem 20', after Brenti), and Stembridge's naturally labeled
$17$-element posets $P$ have polynomials $W(P, x)$ with non-real zeros, so their lattices $J(P)$
have chain polynomials with non-real zeros.

Source: R. P. Stanley, Positivity
Problems and Conjectures in Algebraic Combinatorics (1999), Problem 20' (chain polynomial of a
finite distributive lattice); resolution: Stanley, Positivity Problems (1999), text before Problem
20', citing F. Brenti, Mem. Amer. Math. Soc. 413 (1989), Conj. 3; J. R. Stembridge, Counterexamples
to the poset conjectures of Neggers, Stanley, and Stembridge, Trans. Amer. Math. Soc. 359 (2007),
1115-1128; restated in C. A. Athanasiadis and K. Kalampogia-Evangelinou, Chain enumeration,
partition lattices and polynomials with only real roots, arXiv:2205.03796, Introduction, Stanley:
"When P is natural it can be shown [19, Conj. 3] that Problem 20 is equivalent to the following"
(Problem 20', with L = J(P)); Stembridge, Introduction: naturally labeled posets on 17 vertices with
non-real W-zeros; Athanasiadis–Kalampogia-Evangelinou: for finite distributive lattices the question
is equivalent to the naturally labeled poset conjecture of Neggers, "finally disproved by
Stembridge", https://arxiv.org/abs/2205.03796.
-/
public theorem distributiveLatticeChainPolynomialRealRooted_refuted :
    ¬ distributiveLatticeChainPolynomialRealRooted := by
  intro h
  let a : ℚ := -28 / 43
  let b : ℚ := 1 / 43
  have hle := normSq_eval_le _ (h Point) (⟨a, b⟩ : ℂ)
  have hx : ((⟨a, b⟩ : ℂ).re : ℂ) = ⟨a, (0 : ℚ)⟩ := by
    apply Complex.ext <;> simp
  rw [hx, evalNormSq_spec, evalNormSq_spec] at hle
  have hlt : evalNormSq a b < evalNormSq a 0 := by decide +kernel
  exact (not_lt_of_ge hle) (by exact_mod_cast hlt)

end MathlibExt.Combinatorics.DistributiveLatticeChainPolynomialAMR156Problem0021Wanted
