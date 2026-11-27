/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.List.Forall2
import Mathlib.Order.WellQuasiOrder
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.SpoofLehmerFactorization

/-!
# Finitely many solutions of the Lehmer equation

The Lehmer equation has finitely many solutions in each fixed number of variables at least two.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33, Theorem 1.
-/

namespace MetaMathlibExt

private theorem kappa_set_le (t : List ℝ) (hlen : 2 ≤ t.length)
    (h : ∀ x ∈ t, 2 ≤ x) (i : ℕ) (hi : i < t.length) (y : ℝ) (hy : t[i] ≤ y) :
    lehmerKappa (t.set i y) ≤ lehmerKappa t := by
  rcases hy.lt_or_eq with hlt | heq
  · exact ((lehmerKappa_antitone_bounds t.length hlen t rfl h).2 i hi y hlt).le
  · subst y
    rw [List.set_getElem_self]

private theorem kappa_le_of_forall₂ {s t : List ℝ} (hst : List.Forall₂ (· ≤ ·) s t)
    (p : List ℝ) (hlen : 2 ≤ (p ++ s).length) (h : ∀ x ∈ p ++ s, 2 ≤ x) :
    lehmerKappa (p ++ t) ≤ lehmerKappa (p ++ s) ∧
      (lehmerKappa (p ++ s) ≤ lehmerKappa (p ++ t) → s = t) := by
  induction hst generalizing p with
  | nil => exact ⟨le_rfl, fun _ => rfl⟩
  | @cons x y s t hxy _ ih =>
    have hy : 2 ≤ y := (h x (by simp)).trans hxy
    have hh : ∀ a ∈ (p ++ [y]) ++ s, 2 ≤ a := by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (hp | rfl) | hs
      · exact h a (List.mem_append_left _ hp)
      · exact hy
      · exact h a (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
    have hstep := kappa_set_le (p ++ x :: s) hlen h p.length (by simp) y
      (by simpa using hxy)
    have htail := ih (p ++ [y]) (by simpa using hlen) hh
    simp only [List.append_assoc, List.singleton_append] at htail
    have hstep' : lehmerKappa (p ++ y :: s) ≤ lehmerKappa (p ++ x :: s) := by
      simpa using hstep
    refine ⟨htail.1.trans hstep', ?_⟩
    intro hrev
    have heq : x = y := by
      rcases hxy.lt_or_eq with hlt | heq
      · have hstrict := (lehmerKappa_antitone_bounds (p ++ x :: s).length hlen
          (p ++ x :: s) rfl h).2 p.length (by simp) y (by simpa using hlt)
        have hstrict' : lehmerKappa (p ++ y :: s) < lehmerKappa (p ++ x :: s) := by
          simpa using hstrict
        exact False.elim ((hrev.trans htail.1).not_gt hstrict')
      · exact heq
    subst y
    exact congrArg (List.cons x) (htail.2 hrev)

private theorem kappa_eq (r : ℕ) (x : Fin r → ℕ) (k : ℤ) (hx : ∀ i, 2 ≤ x i)
    (heq : k * ∏ i, ((x i : ℤ) - 1) = ∏ i, (x i : ℤ) - 1) :
    lehmerKappa (List.ofFn fun i => (x i : ℝ)) = k := by
  have hpos : 0 < ∏ i, ((x i : ℝ) - 1) := by
    apply Finset.prod_pos
    intro i _
    have hi : (2 : ℝ) ≤ x i := by exact_mod_cast hx i
    linarith
  simp only [lehmerKappa, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  rw [div_eq_iff hpos.ne']
  have hreal : (k : ℝ) * ∏ i, ((x i : ℝ) - 1) = ∏ i, (x i : ℝ) - 1 := by
    exact_mod_cast heq
  exact hreal.symm

private theorem comparable_solutions_eq (r : ℕ) (hr : 2 ≤ r)
    (x y : Fin r → ℕ) (k l : ℤ) (hx : ∀ i, 2 ≤ x i) (hy : ∀ i, 2 ≤ y i)
    (hk : k * ∏ i, ((x i : ℤ) - 1) = ∏ i, (x i : ℤ) - 1)
    (hl : l * ∏ i, ((y i : ℤ) - 1) = ∏ i, (y i : ℤ) - 1)
    (hkl : k ≤ l) (hxy : x ≤ y) : x = y ∧ k = l := by
  have hrel : List.Forall₂ (· ≤ ·) (List.ofFn fun i => (x i : ℝ))
      (List.ofFn fun i => (y i : ℝ)) := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp, ?_⟩
    intro i hi hj
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact_mod_cast hxy ⟨i, by simpa using hi⟩
  have h := kappa_le_of_forall₂ hrel [] (by simpa using hr) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa using ha)
    exact_mod_cast hx i)
  simp only [List.nil_append, kappa_eq r x k hx hk, kappa_eq r y l hy hl] at h
  have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hlist := h.2 hkl'
  have hfun := List.ofFn_injective hlist
  have heq : x = y := by
    funext i
    exact_mod_cast congrFun hfun i
  refine ⟨heq, ?_⟩
  have heq' : (k : ℝ) = l := le_antisymm hkl' h.1
  exact_mod_cast heq'

/-- **Finitely many solutions of the Lehmer equation in $r$ variables.** For every natural
number $r \ge 2$, there are only finitely many pairs $(k, x)$ of an integer $k > 0$ and a tuple
$x = (x_1, \dots, x_r)$ of natural numbers with $x_i \ge 2$ for every $i$ such that
$k (x_1 - 1) \cdots (x_r - 1) = x_1 \cdots x_r - 1$.

The source also claims that the solutions can be computed explicitly; that claim is not part of
this statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 1 (`integers-2026-A33-thm-1`). -/
public theorem lehmerEquation_solutions_finite (r : ℕ) (hr : 2 ≤ r) :
    {p : ℤ × (Fin r → ℕ) | 0 < p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧
      p.1 * ∏ i, ((p.2 i : ℤ) - 1) = ∏ i, (p.2 i : ℤ) - 1}.Finite := by
  let s : Set (ℕ × (Fin r → ℕ)) :=
    {p | 0 < p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧
      (p.1 : ℤ) * ∏ i, ((p.2 i : ℤ) - 1) = ∏ i, (p.2 i : ℤ) - 1}
  have hs : IsAntichain (· ≤ ·) s := by
    intro p hp q hq hne hpq
    obtain ⟨hxy, hkl⟩ := comparable_solutions_eq r hr p.2 q.2 p.1 q.1
      hp.2.1 hq.2.1 hp.2.2 hq.2.2 (by exact_mod_cast hpq.1) hpq.2
    apply hne
    exact Prod.ext (by exact_mod_cast hkl) hxy
  have hfinite := WellQuasiOrderedLE.finite_of_isAntichain hs
  apply (hfinite.image (fun p : ℕ × (Fin r → ℕ) => ((p.1 : ℤ), p.2))).subset
  intro p hp
  have hk : (p.1.toNat : ℤ) = p.1 := Int.toNat_of_nonneg hp.1.le
  refine ⟨(p.1.toNat, p.2), ?_, ?_⟩
  · change 0 < p.1.toNat ∧ (∀ i, 2 ≤ p.2 i) ∧ _
    have hpos : (0 : ℤ) < (p.1.toNat : ℤ) := by simpa only [hk] using hp.1
    refine ⟨by exact_mod_cast hpos, hp.2.1, ?_⟩
    simpa only [hk] using hp.2.2
  · exact Prod.ext hk rfl

end MetaMathlibExt
