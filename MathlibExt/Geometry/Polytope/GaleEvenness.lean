/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.Faces
public import MathlibExt.Geometry.Polytope.MomentCurve
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Gale's evenness criterion and neighborliness of cyclic polytopes

For parameters `t_1 < ⋯ < t_n`, the facets of the cyclic polytope `C_d(n)` are described by Gale's
evenness condition, and every set of at most `d / 2` vertices spans a face (cyclic polytopes are
neighborly). Both proofs use that a linear functional evaluated along the moment curve
`γ(τ) = (τ, …, τ^d)` is a polynomial of degree at most `d` in `τ` without constant term, and
conversely (G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes",
IAS/Park City Math. Ser. 14 (2004), Example 2.6, arXiv:math/0411400v2).
-/

@[expose] public section

open Polynomial Set

namespace MathlibExt.Geometry.Polytope

/-- **The functional of a polynomial.** For a real polynomial `p`, the linear functional
`x ↦ ∑_{j < d} p_{j+1} x_j` on `ℝ^d`; along the moment curve it equals `p(τ) - p(0)`
(`polyFunctional_momentCurve`). -/
noncomputable def polyFunctional (d : ℕ) (p : ℝ[X]) : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) :=
  ∑ j : Fin d, p.coeff (j.val + 1) • EuclideanSpace.proj j

/-- **A polynomial of degree at most `d` along the moment curve.** For `p` of degree at most `d`,
`polyFunctional d p (γ(τ)) = p(τ) - p(0)`. -/
theorem polyFunctional_momentCurve {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) (τ : ℝ) :
    polyFunctional d p (momentCurve d τ) = p.eval τ - p.coeff 0 := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.sum_range_succ']
  simp only [polyFunctional, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, pow_zero, mul_one,
    add_sub_cancel_right]
  rw [← Fin.sum_univ_eq_sum_range (fun j => p.coeff (j + 1) * τ ^ (j + 1)) d]
  simp

/-- **The polynomial of a functional.** For a linear functional `l` on `ℝ^d`, the polynomial
`∑_{j < d} l(e_j) X^{j+1}`, whose value at `τ` is `l(γ(τ))` (`eval_functionalPoly`). -/
noncomputable def functionalPoly {d : ℕ} (l : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) : ℝ[X] :=
  ∑ j : Fin d, C (l (EuclideanSpace.single j 1)) * X ^ (j.val + 1)

/-- **Evaluating the polynomial of a functional.** `functionalPoly l` evaluated at `τ` is
`l(γ(τ))`. -/
theorem eval_functionalPoly {d : ℕ} (l : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (τ : ℝ) :
    (functionalPoly l).eval τ = l (momentCurve d τ) := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (momentCurve d τ)
  conv_rhs => rw [← h]
  simp only [functionalPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum,
    map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    momentCurve_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Degree of the polynomial of a functional.** `functionalPoly l` has degree at most `d`. -/
theorem natDegree_functionalPoly_le {d : ℕ} (l : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    (functionalPoly l).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **A functional constant on a set is constant on its convex hull.** If `l = c` on `T`, then
`l = c` on `conv T`. -/
theorem eq_of_mem_convexHull_of_forall_eq {T : Set E} {l : StrongDual ℝ E} {c : ℝ}
    (h : ∀ y ∈ T, l y = c) {x : E} (hx : x ∈ convexHull ℝ T) : l x = c :=
  convexHull_min (t := {w | l w = c}) h (convex_hyperplane l.toLinearMap.isLinear c) hx

end General

/-- **Sign of a product of linear factors.** If `τ` differs from every `t_i`, `i ∈ S`, then
`∏_{i ∈ S} (τ - t_i)` has the sign `(-1)^m`, where `m` is the number of `i ∈ S` with `t_i > τ`. -/
theorem neg_one_pow_mul_prod_sub_pos {ι : Type*} (S : Finset ι) (t : ι → ℝ) {τ : ℝ}
    (h : ∀ i ∈ S, t i ≠ τ) :
    0 < (-1 : ℝ) ^ (S.filter fun i => τ < t i).card * ∏ i ∈ S, (τ - t i) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => τ < t i)]
  have h1 : ∏ i ∈ S.filter (fun i => τ < t i), (τ - t i) =
      (-1 : ℝ) ^ (S.filter fun i => τ < t i).card *
        ∏ i ∈ S.filter (fun i => τ < t i), (t i - τ) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hA : 0 < ∏ i ∈ S.filter (fun i => τ < t i), (t i - τ) :=
    Finset.prod_pos fun i hi => sub_pos.2 (Finset.mem_filter.1 hi).2
  have hB : 0 < ∏ i ∈ S.filter (fun i => ¬ τ < t i), (τ - t i) := by
    refine Finset.prod_pos fun i hi => ?_
    obtain ⟨hiS, hlt⟩ := Finset.mem_filter.1 hi
    exact sub_pos.2 (lt_of_le_of_ne (not_lt.1 hlt) (h i hiS))
  rw [h1, ← mul_assoc, ← mul_assoc, ← mul_pow]
  have hone : ((-1 : ℝ) * -1) ^ (S.filter fun i => τ < t i).card = 1 := by norm_num
  rw [hone, one_mul]
  exact mul_pos hA hB

-- Counting elements of `S` above `j`, split at a non-member `k > j`.
private theorem card_filter_lt_eq_add {n : ℕ} (S : Finset (Fin n)) {j k : Fin n} (hk : k ∉ S)
    (hjk : j < k) :
    (S.filter fun i => j < i).card =
      (S.filter fun i => j < i ∧ i < k).card + (S.filter fun i => k < i).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hji⟩
      rcases lt_trichotomy i k with h | rfl | h
      · exact Or.inl ⟨hi, hji, h⟩
      · exact absurd hi hk
      · exact Or.inr ⟨hi, h⟩
    · rintro (⟨hi, h1, -⟩ | ⟨hi, h2⟩)
      · exact ⟨hi, h1⟩
      · exact ⟨hi, hjk.trans h2⟩
  · exact Finset.disjoint_filter.2 fun i _ h1 h2 => lt_asymm h1.2 h2

-- The parity of the gap between two non-members, in terms of signs.
private theorem even_card_filter_iff {n : ℕ} (S : Finset (Fin n)) {j k : Fin n} (hk : k ∉ S)
    (hjk : j < k) :
    Even (S.filter fun i => j < i ∧ i < k).card ↔
      (-1 : ℝ) ^ (S.filter fun i => j < i).card = (-1 : ℝ) ^ (S.filter fun i => k < i).card := by
  rw [card_filter_lt_eq_add S hk hjk, pow_add]
  constructor
  · intro h
    rw [h.neg_one_pow, one_mul]
  · intro h
    have hne : ((-1 : ℝ) ^ (S.filter fun i => k < i).card) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h1 : (-1 : ℝ) ^ (S.filter fun i => j < i ∧ i < k).card = 1 := by
      have := h
      rw [← one_mul ((-1 : ℝ) ^ (S.filter fun i => k < i).card)] at this
      exact mul_right_cancel₀ hne (by simpa using this)
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h1

/-- **Cyclic polytopes are neighborly.** For distinct parameters `t_1, …, t_n` and any set `T` of
at most `d / 2` indices, the points `γ(t_i)`, `i ∈ T`, span a face of the cyclic polytope
`C_d(n) ⊂ ℝ^d`: it is cut out by the functional corresponding to `-∏_{i ∈ T} (τ - t_i)^2`
(Ziegler, PCMI lecture notes, arXiv:math/0411400v2, Example 2.6). -/
theorem isExposed_cyclicPolytope_of_two_mul_card_le {d n : ℕ} {t : Fin n → ℝ}
    (ht : Function.Injective t) (T : Finset (Fin n)) (hT : 2 * T.card ≤ d) :
    IsExposed ℝ (cyclicPolytope d t)
      (convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin n)))) := by
  classical
  set q : ℝ[X] := ∏ i ∈ T, (X - C (t i)) with hq
  have hqdeg : q.natDegree = T.card := natDegree_finsetProd_X_sub_C_eq_card T t
  set p : ℝ[X] := -(q * q) with hp
  have hpdeg : p.natDegree ≤ d := by
    rw [hp, natDegree_neg]
    exact natDegree_mul_le.trans (by omega)
  have hpeval : ∀ τ, p.eval τ = -(q.eval τ * q.eval τ) := fun τ => by simp [hp]
  have hqeval : ∀ j, q.eval (t j) = 0 ↔ j ∈ T := by
    intro j
    simp only [hq, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, sub_eq_zero]
    exact ⟨fun ⟨i, hi, h⟩ => ht h ▸ hi, fun h => ⟨j, h, rfl⟩⟩
  refine isExposed_convexHull_of_forall_le (cyclicVertices d t) _ (polyFunctional d p)
    (-p.coeff 0) ?_ ?_ ?_
  · intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    rw [polyFunctional_momentCurve hpdeg, hpeval]
    nlinarith [mul_self_nonneg (q.eval (t j))]
  · rintro y ⟨i, hi, rfl⟩
    refine ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [polyFunctional_momentCurve hpdeg, hpeval, (hqeval i).2 hi]
    ring
  · intro y hy hly
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    rw [polyFunctional_momentCurve hpdeg, hpeval] at hly
    have h0 : q.eval (t j) = 0 := by nlinarith [mul_self_nonneg (q.eval (t j))]
    exact ⟨j, (hqeval j).1 h0, rfl⟩

/-- **Gale's evenness criterion.** Let `t_1 < ⋯ < t_n` and let `S` be a set of `d` indices. Then
the points `γ(t_i)`, `i ∈ S`, of the moment curve span a face of the cyclic polytope
`C_d(n) ⊂ ℝ^d` (for `n > d` necessarily a facet, as they are affinely independent) if and only
if `S` satisfies Gale's evenness condition: any two indices outside `S` are separated by an even
number of elements of `S` (D. Gale, "Neighborly and cyclic polytopes", Proc. Sympos. Pure Math. 7
(1963); Ziegler, PCMI lecture notes, arXiv:math/0411400v2, Example 2.6). -/
theorem isExposed_cyclicPolytope_iff_galeEvenness {d n : ℕ} {t : Fin n → ℝ} (ht : StrictMono t)
    (S : Finset (Fin n)) (hS : S.card = d) :
    IsExposed ℝ (cyclicPolytope d t)
        (convexHull ℝ ((fun i => momentCurve d (t i)) '' (S : Set (Fin n)))) ↔
      GaleEvenness S := by
  classical
  set q : ℝ[X] := ∏ i ∈ S, (X - C (t i)) with hq
  have hqdeg : q.natDegree = d := (natDegree_finsetProd_X_sub_C_eq_card S t).trans hS
  have hqroot : ∀ i ∈ S, q.eval (t i) = 0 := fun i hi => by
    simp only [hq, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hi (sub_self _)
  -- the sign of `q` at a non-member
  have hsign : ∀ j ∉ S, 0 < (-1 : ℝ) ^ (S.filter fun i => j < i).card * q.eval (t j) := by
    intro j hj
    have h := neg_one_pow_mul_prod_sub_pos S t (τ := t j)
      (fun i hi h => hj (ht.injective h ▸ hi))
    have hfil : (S.filter fun i => t j < t i) = S.filter fun i => j < i :=
      Finset.filter_congr fun i _ => ht.lt_iff_lt
    rw [hfil] at h
    simpa [hq, eval_prod] using h
  constructor
  · -- a face forces the evenness condition
    intro hexp
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · intro j k _ _ _
      simp
    have hmem : ∀ i, momentCurve d (t i) ∈ cyclicPolytope d t := fun i =>
      subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    have hF0 : momentCurve d (t i0) ∈
        convexHull ℝ ((fun i => momentCurve d (t i)) '' (S : Set (Fin n))) :=
      subset_convexHull ℝ _ ⟨i0, hi0, rfl⟩
    obtain ⟨l, hl⟩ := hexp ⟨_, hF0⟩
    have hmaxS : ∀ i ∈ S, ∀ y ∈ cyclicPolytope d t, l y ≤ l (momentCurve d (t i)) := by
      intro i hi
      have h : momentCurve d (t i) ∈
          convexHull ℝ ((fun i => momentCurve d (t i)) '' (S : Set (Fin n))) :=
        subset_convexHull ℝ _ ⟨i, hi, rfl⟩
      rw [hl] at h
      exact h.2
    set V := l (momentCurve d (t i0)) with hV
    have hVi : ∀ i ∈ S, l (momentCurve d (t i)) = V := fun i hi =>
      le_antisymm (hmaxS i0 hi0 _ (hmem i)) (hmaxS i hi _ (hmem i0))
    have hlt : ∀ j ∉ S, l (momentCurve d (t j)) < V := by
      intro j hj
      refine lt_of_le_of_ne (hmaxS i0 hi0 _ (hmem j)) fun heq => ?_
      have hjF : momentCurve d (t j) ∈
          convexHull ℝ ((fun i => momentCurve d (t i)) '' (S : Set (Fin n))) := by
        rw [hl]
        exact ⟨hmem j, fun y hy => heq ▸ hmaxS i0 hi0 y hy⟩
      have h := eq_of_mem_convexHull_of_forall_eq (l := polyFunctional d q) (c := -q.coeff 0)
        (by
          rintro y ⟨i, hi, rfl⟩
          rw [polyFunctional_momentCurve hqdeg.le, hqroot i hi]
          ring) hjF
      rw [polyFunctional_momentCurve hqdeg.le] at h
      have h0 : q.eval (t j) = 0 := by linarith
      have := hsign j hj
      rw [h0, mul_zero] at this
      exact lt_irrefl _ this
    set g : ℝ[X] := C V - functionalPoly l with hg
    have hgeval : ∀ τ, g.eval τ = V - l (momentCurve d τ) := fun τ => by
      simp [hg, eval_functionalPoly]
    have hgdeg : g.natDegree ≤ d := by
      rw [hg]
      refine (natDegree_sub_le _ _).trans (max_le ?_ (natDegree_functionalPoly_le l))
      rw [natDegree_C]
      exact Nat.zero_le _
    intro j k hj hk hjk
    have hgj : 0 < g.eval (t j) := by rw [hgeval]; linarith [hlt j hj]
    have hgk : 0 < g.eval (t k) := by rw [hgeval]; linarith [hlt k hk]
    have hg0 : g ≠ 0 := fun h => by rw [h, eval_zero] at hgj; exact lt_irrefl _ hgj
    have hdvd : q ∣ g := by
      refine Finset.prod_dvd_of_coprime
        (fun a _ b _ hab => pairwise_coprime_X_sub_C ht.injective hab) fun i hi => ?_
      rw [dvd_iff_isRoot, IsRoot, hgeval, hVi i hi, sub_self]
    obtain ⟨r, hr⟩ := hdvd
    have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact hg0 hr
    have hqmonic : q.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (t i)
    have hrdeg : r.natDegree = 0 := by
      have := hqmonic.natDegree_mul' hr0
      rw [← hr, hqdeg] at this
      omega
    have hgc : ∀ τ, g.eval τ = q.eval τ * r.coeff 0 := fun τ => by
      rw [hr, eval_mul]
      congr 1
      conv_lhs => rw [eq_C_of_natDegree_eq_zero hrdeg]
      exact eval_C
    rw [hgc] at hgj hgk
    have hqq : 0 < q.eval (t j) * q.eval (t k) := by
      have := mul_pos hgj hgk
      have hc0 : r.coeff 0 ≠ 0 := fun h => by
        rw [h, mul_zero] at hgj
        exact lt_irrefl _ hgj
      have hc : 0 < r.coeff 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc0))
      nlinarith
    have hsj := hsign j hj
    have hsk := hsign k hk
    rw [even_card_filter_iff S hk hjk]
    rcases neg_one_pow_eq_or ℝ (S.filter fun i => j < i).card with h1 | h1 <;>
      rcases neg_one_pow_eq_or ℝ (S.filter fun i => k < i).card with h2 | h2
    · rw [h1, h2]
    · rw [h1] at hsj; rw [h2] at hsk; nlinarith
    · rw [h1] at hsj; rw [h2] at hsk; nlinarith
    · rw [h1, h2]
  · -- the evenness condition gives a supporting functional
    intro hG
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ∀ j ∉ S, (-1 : ℝ) ^ (S.filter fun i => j < i).card = ε := by
      by_cases h : ∃ j0, j0 ∉ S
      · obtain ⟨j0, hj0⟩ := h
        refine ⟨(-1 : ℝ) ^ (S.filter fun i => j0 < i).card, fun j hj => ?_⟩
        rcases lt_trichotomy j j0 with h | rfl | h
        · exact (even_card_filter_iff S hj0 h).1 (hG j j0 hj hj0 h)
        · rfl
        · exact ((even_card_filter_iff S hj h).1 (hG j0 j hj0 hj h)).symm
      · exact ⟨1, fun j hj => absurd ⟨j, hj⟩ h⟩
    set p : ℝ[X] := -(C ε * q) with hp
    have hpdeg : p.natDegree ≤ d := by
      rw [hp, natDegree_neg]
      exact (natDegree_C_mul_le _ _).trans hqdeg.le
    have hpeval : ∀ τ, p.eval τ = -(ε * q.eval τ) := fun τ => by simp [hp]
    refine isExposed_convexHull_of_forall_le (cyclicVertices d t) _ (polyFunctional d p)
      (-p.coeff 0) ?_ ?_ ?_
    · intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      rw [polyFunctional_momentCurve hpdeg, hpeval]
      by_cases hj : j ∈ S
      · rw [hqroot j hj]; simp
      · have := hsign j hj
        rw [hε j hj] at this
        linarith
    · rintro y ⟨i, hi, rfl⟩
      refine ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [polyFunctional_momentCurve hpdeg, hpeval, hqroot i hi]
      ring
    · intro y hy hly
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      by_cases hj : j ∈ S
      · exact ⟨j, hj, rfl⟩
      · rw [polyFunctional_momentCurve hpdeg, hpeval] at hly
        have := hsign j hj
        rw [hε j hj] at this
        linarith

/-- **Every vertex set of a cyclic simplex spans a face.** For `d + 1` distinct parameters, the
cyclic polytope `C_d(d+1)` is a `d`-simplex, and for every set `T` of indices the points
`γ(t_i)`, `i ∈ T`, span a face of it that contains no other `γ(t_j)`. The face is cut out by the
functional of the Lagrange interpolation polynomial equal to `0` at the `t_i`, `i ∈ T`, and to
`-1` at the other parameters. -/
theorem isExposed_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t)
    (T : Finset (Fin (d + 1))) :
    IsExposed ℝ (cyclicPolytope d t)
        (convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1))))) ∧
      ∀ j, momentCurve d (t j) ∈
          convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1)))) → j ∈ T := by
  classical
  have hinj : Set.InjOn t (Finset.univ : Finset (Fin (d + 1))) := ht.injOn
  set r : Fin (d + 1) → ℝ := fun i => if i ∈ T then 0 else 1 with hr
  set q : ℝ[X] := Lagrange.interpolate Finset.univ t r with hq
  have hqeval : ∀ i, q.eval (t i) = r i := fun i =>
    Lagrange.eval_interpolate_at_node r hinj (Finset.mem_univ i)
  have hqdeg : q.natDegree ≤ d := by
    have h := Lagrange.degree_interpolate_lt (r := r) hinj
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact natDegree_le_of_degree_le (Order.le_of_lt_succ (by exact_mod_cast h))
  set p : ℝ[X] := -q with hp
  have hpdeg : p.natDegree ≤ d := by rw [hp, natDegree_neg]; exact hqdeg
  have hl : ∀ i, polyFunctional d p (momentCurve d (t i)) =
      -(if i ∈ T then 0 else 1) - p.coeff 0 := fun i => by
    rw [polyFunctional_momentCurve hpdeg, hp, eval_neg, hqeval]
  constructor
  · refine isExposed_convexHull_of_forall_le (cyclicVertices d t) _ (polyFunctional d p)
      (-p.coeff 0) ?_ ?_ ?_
    · intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hl]
      split_ifs <;> linarith
    · rintro y ⟨i, hi, rfl⟩
      refine ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [hl]
      simp [Finset.mem_coe.1 hi]
    · intro y hy hly
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hl] at hly
      by_cases hj : j ∈ T
      · exact ⟨j, hj, rfl⟩
      · simp only [hj, ite_false] at hly
        linarith
  · intro j hj
    by_contra hjT
    have h := eq_of_mem_convexHull_of_forall_eq (l := polyFunctional d p) (c := -p.coeff 0)
      (by
        rintro y ⟨i, hi, rfl⟩
        rw [hl]
        simp [Finset.mem_coe.1 hi]) hj
    rw [hl] at h
    simp only [hjT, ite_false] at h
    linarith

/-- **The faces of a cyclic simplex.** For `d + 1` distinct parameters, the faces of `C_d(d+1)`
are exactly the convex hulls of the sets of vertices `γ(t_i)`, `i ∈ T`, for `T` ranging over all
sets of indices. -/
theorem mem_faces_cyclicSimplex_iff {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t)
    {F : Set (EuclideanSpace ℝ (Fin d))} :
    F ∈ faces (cyclicVertices d t) ↔ ∃ T : Finset (Fin (d + 1)),
      F = convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1)))) := by
  classical
  constructor
  · intro hF
    refine ⟨Finset.univ.filter fun i => momentCurve d (t i) ∈ F, ?_⟩
    refine (eq_convexHull_inter_of_mem_faces hF).trans ?_
    congr 1
    ext y
    simp only [Set.mem_inter_iff, cyclicVertices, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, Finset.coe_filter, Set.mem_image, Set.mem_ofPred_eq,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hyF, i, rfl⟩
      exact ⟨i, hyF, rfl⟩
    · rintro ⟨i, hiF, rfl⟩
      exact ⟨hiF, i, rfl⟩
  · rintro ⟨T, rfl⟩
    exact (isExposed_cyclicSimplex ht T).1

/-- **Dimension of a face of a cyclic simplex.** For `d + 1` distinct parameters and any set `T`
of indices, the affine hull of `conv {γ(t_i) : i ∈ T}` has dimension `|T| - 1` (read as `0` for
`T = ∅`), because these points are affinely independent. -/
theorem finrank_direction_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ}
    (ht : Function.Injective t) (T : Finset (Fin (d + 1))) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ
      ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1)))))).direction = T.card - 1 := by
  classical
  rw [affineSpan_convexHull, direction_affineSpan]
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  have hind : AffineIndependent ℝ (fun i : (T : Set (Fin (d + 1))) => momentCurve d (t i)) :=
    (affineIndependent_momentCurve le_rfl ht).comp_embedding (Function.Embedding.subtype _)
  have hrange : Set.range (fun i : (T : Set (Fin (d + 1))) => momentCurve d (t i)) =
      (fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1))) := by
    ext y
    simp
  rw [← hrange]
  exact hind.finrank_vectorSpan (by simp; have := hT.card_pos; omega)

/-- **Face numbers of a cyclic simplex.** For `d + 1` distinct parameters, the polytope
`C_d(d+1) = conv {γ(t_0), …, γ(t_d)}` is a `d`-simplex and has `f_k = C(d+1, k+1)` faces of
dimension `k` for every `k`. For `d = 2` this is a triangle, with f-vector `(3, 3)` and
`f_2 = 1`. -/
theorem faceNumber_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t)
    (k : ℕ) : faceNumber (cyclicVertices d t) k = (d + 1).choose (k + 1) := by
  classical
  set g : Finset (Fin (d + 1)) → Set (EuclideanSpace ℝ (Fin d)) :=
    fun T => convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1)))) with hg
  have hginj : Function.Injective g := by
    intro T T' h
    ext j
    constructor
    · intro hj
      refine (isExposed_cyclicSimplex ht T').2 j ?_
      have : momentCurve d (t j) ∈ g T := subset_convexHull ℝ _ ⟨j, hj, rfl⟩
      rwa [h] at this
    · intro hj
      refine (isExposed_cyclicSimplex ht T).2 j ?_
      have : momentCurve d (t j) ∈ g T' := subset_convexHull ℝ _ ⟨j, hj, rfl⟩
      rwa [← h] at this
  have hne : ∀ T : Finset (Fin (d + 1)), (g T).Nonempty ↔ T.Nonempty := by
    intro T
    constructor
    · rintro ⟨x, hx⟩
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [hg, h] at hx
    · rintro ⟨i, hi⟩
      exact ⟨_, subset_convexHull ℝ _ ⟨i, hi, rfl⟩⟩
  have hset : {F | F ∈ faces (cyclicVertices d t) ∧ F.Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = k} = g '' {T | T.card = k + 1} := by
    ext F
    constructor
    · rintro ⟨hF, hFne, hdim⟩
      obtain ⟨T, rfl⟩ := (mem_faces_cyclicSimplex_iff ht).1 hF
      refine ⟨T, ?_, rfl⟩
      have hT := ((hne T).1 hFne).card_pos
      rw [finrank_direction_cyclicSimplex ht] at hdim
      change T.card = k + 1
      omega
    · rintro ⟨T, hT, rfl⟩
      change T.card = k + 1 at hT
      refine ⟨(mem_faces_cyclicSimplex_iff ht).2 ⟨T, rfl⟩, (hne T).2 ?_, ?_⟩
      · exact Finset.card_pos.1 (by omega)
      · rw [finrank_direction_cyclicSimplex ht]
        omega
  rw [faceNumber, hset, Set.ncard_image_of_injective _ hginj]
  have hT : {T : Finset (Fin (d + 1)) | T.card = k + 1} =
      ((Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin (d + 1)))) :
        Set (Finset (Fin (d + 1)))) := by
    ext T
    simp
  rw [hT, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Dimension of a cyclic simplex.** For `d + 1` distinct parameters, `C_d(d+1)` has
dimension `d`. -/
theorem dim_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t) :
    dim (cyclicVertices d t) = d := by
  have hc : ((cyclicVertices d t : Finset (EuclideanSpace ℝ (Fin d))) :
      Set (EuclideanSpace ℝ (Fin d))) =
      (fun i => momentCurve d (t i)) ''
        ((Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) := by
    simp [cyclicVertices]
  rw [dim, hc, finrank_direction_cyclicSimplex ht]
  simp

/-- **The vertices of a cyclic simplex.** For `d + 1` distinct parameters, every point
`γ(t_i)` is a vertex (extreme point) of `C_d(d+1)`, and these are all its vertices. -/
theorem extremePoints_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t) :
    (cyclicPolytope d t).extremePoints ℝ =
      ((cyclicVertices d t : Finset (EuclideanSpace ℝ (Fin d))) :
        Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  refine Set.Subset.antisymm extremePoints_convexHull_subset ?_
  intro y hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
  have h := (isExposed_cyclicSimplex ht {i}).1
  simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton] at h
  exact h.isExtreme.mem_extremePoints

/-- **A cyclic simplex is simplicial.** For `d + 1` distinct parameters, every facet of `C_d(d+1)`
contains exactly `d` of its vertices. -/
theorem isSimplicial_cyclicSimplex {d : ℕ} {t : Fin (d + 1) → ℝ} (ht : Function.Injective t) :
    IsSimplicial (cyclicVertices d t) := by
  classical
  intro F hF hne hdim
  obtain ⟨T, rfl⟩ := (mem_faces_cyclicSimplex_iff ht).1 hF
  rw [finrank_direction_cyclicSimplex ht, dim_cyclicSimplex ht] at hdim
  rw [dim_cyclicSimplex ht]
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hne
    simp [h] at hx
  have hTcard : T.card = d := by have := hTne.card_pos; omega
  have hd : 1 ≤ d := by have := hTne.card_pos; omega
  have hinter : convexHull ℝ ((fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1)))) ∩
      (cyclicPolytope d t).extremePoints ℝ =
      (fun i => momentCurve d (t i)) '' (T : Set (Fin (d + 1))) := by
    rw [extremePoints_cyclicSimplex ht]
    ext y
    constructor
    · rintro ⟨hyF, hy⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨j, (isExposed_cyclicSimplex ht T).2 j hyF, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨subset_convexHull ℝ _ ⟨i, hi, rfl⟩,
        Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
  change (_ ∩ (cyclicPolytope d t).extremePoints ℝ).ncard = d
  rw [hinter, Set.ncard_image_of_injective (f := fun i => momentCurve d (t i)) _
    ((momentCurve_injective hd).comp ht), Set.ncard_coe_finset, hTcard]

end MathlibExt.Geometry.Polytope
