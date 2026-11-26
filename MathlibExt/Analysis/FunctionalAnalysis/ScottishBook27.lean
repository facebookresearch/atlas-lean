/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Bézout identity for continuous polynomials

Two continuous polynomials without a common zero on a complex Banach space
generate the unit ideal in the algebra of continuous polynomials.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted

/-- **Continuous polynomial functions on a complex normed space.** Let $E$ be a complex normed
space. A function $F : E \to \mathbb{C}$ is a continuous polynomial function if there are a
natural number $n$, natural numbers $m_1, \dots, m_n$ and continuous $\mathbb{C}$-multilinear
maps $A_i : E^{m_i} \to \mathbb{C}$, with $A_i$ taking $m_i$ arguments, such that
$F(x) = \sum_{i=1}^{n} A_i(x, \dots, x)$ for every $x \in E$.

A $0$-multilinear map is a constant, so constant functions are polynomial functions. -/
def IsPolynomialOn (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) : Prop :=
  ∃ (n : ℕ) (m : Fin n → ℕ)
    (A : (i : Fin n) → (E [× m i]→L[ℂ] ℂ)),
    ∀ x, F x = ∑ i, A i fun _ => x

open Polynomial
open scoped Polynomial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem polynomial_sum_diagonal {ι : Type} [Fintype ι] (m : ι → ℕ)
    (A : (i : ι) → E [×m i]→L[ℂ] ℂ) {f : E → ℂ}
    (h : ∀ x, f x = ∑ i, A i fun _ => x) : IsPolynomialOn E f := by
  classical
  let e := (Fintype.equivFin ι).symm
  exact ⟨_, fun i => m (e i), fun i => A (e i), fun x =>
    (h x).trans (e.sum_comp (fun i => A i fun _ => x)).symm⟩

private theorem polynomial_diagonal {m : ℕ} (A : E [×m]→L[ℂ] ℂ) :
    IsPolynomialOn E (fun x => A fun _ => x) :=
  ⟨1, fun _ => m, fun _ => A, by simp⟩

private theorem polynomial_const (c : ℂ) : IsPolynomialOn E (fun _ => c) :=
  polynomial_diagonal (m := 0) (ContinuousMultilinearMap.constOfIsEmpty ℂ _ c)

private theorem polynomial_add {f g : E → ℂ} (hf : IsPolynomialOn E f) (hg : IsPolynomialOn E g) :
    IsPolynomialOn E (f + g) := by
  obtain ⟨n, m, A, hA⟩ := hf
  obtain ⟨k, l, B, hB⟩ := hg
  apply polynomial_sum_diagonal (Sum.elim m l) (fun i => Sum.rec (motive := fun i =>
    E [×Sum.elim m l i]→L[ℂ] ℂ) A B i)
  intro x
  simp [Fintype.sum_sum_type, hA, hB]
  rfl

private theorem polynomial_mul {f g : E → ℂ} (hf : IsPolynomialOn E f) (hg : IsPolynomialOn E g) :
    IsPolynomialOn E (f * g) := by
  classical
  obtain ⟨n, m, A, hA⟩ := hf
  obtain ⟨k, l, B, hB⟩ := hg
  apply polynomial_sum_diagonal (fun i : Fin n × Fin k => m i.1 + l i.2)
    (fun i => (((A i.1).smulRight (B i.2)).uncurrySum).domDomCongr finSumFinEquiv)
  intro x
  rw [Pi.mul_apply, hA, hB, Finset.sum_mul, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  rfl

private def polynomialAlgebra (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Subalgebra ℂ (E → ℂ) where
  carrier := {f | IsPolynomialOn E f}
  add_mem' := polynomial_add
  mul_mem' := polynomial_mul
  algebraMap_mem' := polynomial_const
  zero_mem' := polynomial_const 0
  one_mem' := polynomial_const 1

private def atPoint (x : E) : polynomialAlgebra E →+* ℂ :=
  (Pi.evalRingHom _ x).comp (polynomialAlgebra E).val.toRingHom

private theorem polynomial_eq_const_of_ne_zero {f : E → ℂ} (hf : IsPolynomialOn E f)
    (h : ∀ x, f x ≠ 0) (x : E) : f x = f 0 := by
  classical
  obtain ⟨n, m, A, hA⟩ := hf
  let p : ℂ[X] := ∑ i, monomial (m i) (A i fun _ => x)
  have heval (t : ℂ) : p.eval t = f (t • x) := by
    rw [hA]
    simp [p, eval_finsetSum, ContinuousMultilinearMap.map_smul_univ, mul_comm]
  have hd : p.natDegree = 0 := by
    by_contra hd
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p (degree_ne_of_natDegree_ne hd)
    exact h _ ((heval t).symm.trans ht)
  have heq : p.eval 1 = p.eval 0 := by
    obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hd
    rw [← hc]
    simp
  simpa [heval] using heq

/-- A mixed term in the expansion at `x + t • v`, before multiplication by `t ^ s.card`. -/
private noncomputable def mixedTerm {m : ℕ} (A : E [×m]→L[ℂ] ℂ) (v : E)
    (s : Finset (Fin m)) : polynomialAlgebra E :=
  ⟨fun x => A (s.piecewise (fun _ => v) fun _ => x), by
    let B := ContinuousMultilinearMap.curryFinFinset ℂ E ℂ (s := s) rfl rfl A (fun _ => v)
    exact (show (fun x => B fun _ => x) = _ from funext fun x =>
      ContinuousMultilinearMap.curryFinFinset_apply_const rfl rfl A v x) ▸ polynomial_diagonal B⟩

private noncomputable def diagonalLine {m : ℕ} (A : E [×m]→L[ℂ] ℂ) (v : E) :
    (polynomialAlgebra E)[X] :=
  ∑ s : Finset (Fin m), monomial s.card (mixedTerm A v s)

private theorem diagonalLine_eval {m : ℕ} (A : E [×m]→L[ℂ] ℂ) (v x : E) (t : ℂ) :
    ((diagonalLine A v).map (atPoint x)).eval t = A fun _ => t • v + x := by
  classical
  rw [show (fun _ : Fin m => t • v + x) = (fun _ => t • v) + (fun _ => x) from rfl,
    A.map_add_univ]
  simp only [diagonalLine, Polynomial.map_sum, map_monomial, eval_finsetSum, eval_monomial]
  apply Finset.sum_congr rfl
  intro s _
  let B := ContinuousMultilinearMap.curryFinFinset ℂ E ℂ (s := s) rfl rfl A
  rw [← ContinuousMultilinearMap.curryFinFinset_apply_const (s := s) rfl rfl]
  change A (s.piecewise (fun _ => v) fun _ => x) * t ^ s.card =
    (B (fun _ => t • v)) fun _ => x
  rw [B.map_smul_univ (fun _ => t) (fun _ => v)]
  simp [B, ContinuousMultilinearMap.curryFinFinset_apply_const, mul_comm,
    -ContinuousMultilinearMap.curryFinFinset_apply]

private theorem diagonalLine_degree {m : ℕ} (A : E [×m]→L[ℂ] ℂ) (v : E) :
    (diagonalLine A v).natDegree ≤ m :=
  natDegree_sum_le_of_forall_le _ _ fun s _ =>
    (natDegree_monomial_le _).trans (by simpa using s.card_le_univ)

private theorem diagonalLine_top {m : ℕ} (A : E [×m]→L[ℂ] ℂ) (v x : E) :
    atPoint x ((diagonalLine A v).coeff m) = A fun _ => v := by
  classical
  simp only [diagonalLine, finsetSum_coeff, map_sum]
  rw [Finset.sum_eq_single Finset.univ]
  · simp [atPoint, mixedTerm, coeff_monomial]
  · intro s _ hs
    have hlt : s.card < m := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
    simp [coeff_monomial, hlt.ne]
  · simp

/-- Discard vanishing top homogeneous parts until one survives in some direction. -/
private theorem exists_top_part {ι : Type} (m : ι → ℕ) (A : (i : ι) → E [×m i]→L[ℂ] ℂ)
    {f : E → ℂ} (hne : ∃ x, f x ≠ 0) (s : Finset ι)
    (hs : ∀ x, f x = ∑ i ∈ s, A i fun _ => x) :
    ∃ (u : Finset ι) (d : ℕ) (v : E),
      (∀ x, f x = ∑ i ∈ u, A i fun _ => x) ∧ (∀ i ∈ u, m i ≤ d) ∧
      (∑ i ∈ u with m i = d, A i fun _ => v) ≠ 0 := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hnonempty : s.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      contrapose! hx
      simpa [hx] using hs x
    obtain ⟨j, hj, hmax⟩ := s.exists_max_image m hnonempty
    by_cases h : ∃ v, (∑ i ∈ s with m i = m j, A i fun _ => v) ≠ 0
    · obtain ⟨v, hv⟩ := h
      exact ⟨s, m j, v, hs, hmax, hv⟩
    push Not at h
    apply ih (s.filter fun i => m i ≠ m j)
    · exact Finset.filter_ssubset.mpr ⟨j, hj, not_not_intro rfl⟩
    · intro x
      rw [hs, ← Finset.sum_filter_add_sum_filter_not s (fun i => m i = m j), h, zero_add]

private theorem line_of_sum {ι : Type} {m : ι → ℕ} (A : (i : ι) → E [×m i]→L[ℂ] ℂ)
    (s : Finset ι) {f : E → ℂ} (hs : ∀ x, f x = ∑ i ∈ s, A i fun _ => x) (v x : E) (t : ℂ) :
    ((∑ i ∈ s, diagonalLine (A i) v).map (atPoint x)).eval t = f (t • v + x) := by
  simp [Polynomial.map_sum, eval_finsetSum, diagonalLine_eval, hs]

/-- Choose a line direction preserving the first polynomial's degree at every base point. -/
private theorem regular_line {f : E → ℂ} (hf : IsPolynomialOn E f) (hne : ∃ x, f x ≠ 0) :
    ∃ (v : E) (p : (polynomialAlgebra E)[X]) (d : ℕ), p.natDegree ≤ d ∧
      (∀ x, atPoint x (p.coeff d) ≠ 0) ∧
      ∀ x t, (p.map (atPoint x)).eval t = f (t • v + x) := by
  classical
  obtain ⟨n, m, A, h⟩ := hf
  obtain ⟨s, d, v, hs, hbound, hv⟩ := exists_top_part m A hne Finset.univ h
  refine ⟨v, ∑ i ∈ s, diagonalLine (A i) v, d, ?_, ?_, line_of_sum A s hs v⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (diagonalLine_degree _ _).trans (hbound i hi)
  · intro x
    rw [finsetSum_coeff, map_sum]
    rw [Finset.sum_filter] at hv
    convert hv using 1
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with heq
    · rw [← heq, diagonalLine_top]
    · have hlt := (diagonalLine_degree (A i) v).trans_lt (lt_of_le_of_ne (hbound i hi) heq)
      simp [coeff_eq_zero_of_natDegree_lt hlt]

private theorem resultant_atPoint_ne_zero {f g : E → ℂ} {v : E}
    {p q : (polynomialAlgebra E)[X]} {d n : ℕ} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ n)
    (hlead : ∀ x, atPoint x (p.coeff d) ≠ 0)
    (hpval : ∀ x t, (p.map (atPoint x)).eval t = f (t • v + x))
    (hqval : ∀ x t, (q.map (atPoint x)).eval t = g (t • v + x))
    (hfg : ∀ x, f x = 0 → g x ≠ 0) (x : E) : atPoint x (p.resultant q d n) ≠ 0 := by
  let e := atPoint x
  have hd : (p.map e).natDegree = d :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_map_le.trans hp) (by simpa [e] using hlead x)
  rw [← resultant_map_map, ← hd, resultant_eq_prod_eval _ _ _ (natDegree_map_le.trans hq)
    (IsAlgClosed.splits _)]
  apply mul_ne_zero
  · apply pow_ne_zero
    rw [← coeff_natDegree, hd, coeff_map]
    exact hlead x
  · apply Multiset.prod_ne_zero
    intro h
    obtain ⟨t, ht, hzero⟩ := Multiset.mem_map.mp h
    exact hfg _ ((hpval x t).symm.trans (mem_roots'.mp ht).2) ((hqval x t).symm.trans hzero)

/--
**Bezout identity for polynomials without a common zero.** Let $E$ be a complex Banach space
and let $F, G : E \to \mathbb{C}$ be continuous polynomial functions with no common zero, that
is, $G(x) \neq 0$ whenever $F(x) = 0$. Then there are continuous polynomial functions
$\varphi, \psi : E \to \mathbb{C}$ such that $F(x) \varphi(x) + G(x) \psi(x) = 1$ for every
$x \in E$.

This is the identity recorded in the addendum to Problem 27 of the Scottish Book (Mazur-Orlicz,
4 April 1939). The problem asks whether two complex polynomials on a complex Banach space that
both tend to $0$ along a sequence $(x_n)$ in the unit ball must have a common zero. The answer
is positive and follows from the identity by contradiction: continuous polynomials are bounded
on the unit ball, so $F(x_n) \varphi(x_n) + G(x_n) \psi(x_n)$ would tend to $0$, yet it equals
$1$.

Source: S. Mazur and W. Orlicz, Problem 27 of the Scottish Book, with the
positive answer via the Bezout identity in the addendum; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem bezout_identity_for_polynomials_without_common_zero :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (F G : E → ℂ),
      IsPolynomialOn E F → IsPolynomialOn E G →
      (∀ x, F x = 0 → G x ≠ 0) →
      ∃ (φ ψ : E → ℂ), IsPolynomialOn E φ ∧ IsPolynomialOn E ψ ∧
        ∀ x, F x * φ x + G x * ψ x = 1 := by
  classical
  intro E _ _ _ F G hF hG hFG
  by_cases hFne : ∃ x, F x ≠ 0
  · obtain ⟨v, p, d, hp, hlead, hpval⟩ := regular_line hF hFne
    obtain ⟨k, m, A, hA⟩ := hG
    let q := ∑ i, diagonalLine (A i) v
    have hqval (x : E) (t : ℂ) : (q.map (atPoint x)).eval t = G (t • v + x) :=
      line_of_sum A Finset.univ hA v x t
    -- A positive second degree bound also covers two constant restrictions.
    let r := p.resultant q d (q.natDegree + 1)
    have hr (x : E) : atPoint x r ≠ 0 :=
      resultant_atPoint_ne_zero hp (Nat.le_succ _) hlead hpval hqval hFG x
    have hconst (x : E) : atPoint x r = atPoint 0 r :=
      polynomial_eq_const_of_ne_zero r.property hr x
    obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant p q hp
      (Nat.le_succ q.natDegree) (Or.inr (Nat.succ_ne_zero _))
    let c := (atPoint 0 r)⁻¹
    refine ⟨fun x => atPoint x (a.coeff 0) * c, fun x => atPoint x (b.coeff 0) * c,
      polynomial_mul (a.coeff 0).property (polynomial_const c),
      polynomial_mul (b.coeff 0).property (polynomial_const c), ?_⟩
    intro x
    have h : F x * atPoint x (a.coeff 0) + G x * atPoint x (b.coeff 0) = atPoint x r := by
      simpa only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C,
        hpval, hqval, zero_smul, zero_add, ← coeff_zero_eq_eval_zero, coeff_map] using
        congrArg (fun P : (polynomialAlgebra E)[X] => (P.map (atPoint x)).eval 0) hab
    rw [← mul_assoc, ← mul_assoc, ← add_mul, h, hconst]
    exact mul_inv_cancel₀ (hr 0)
  · push Not at hFne
    have hGne (x : E) := hFG x (hFne x)
    refine ⟨fun _ => 0, fun _ => (G 0)⁻¹, polynomial_const _, polynomial_const _, fun x => ?_⟩
    rw [mul_zero, zero_add, polynomial_eq_const_of_ne_zero hG hGne x, mul_inv_cancel₀ (hGne 0)]

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted
