/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Homogeneous forms on linear recurrences

For an independent family of bilateral solutions of an order-`k` recurrence, a degree-`k`
homogeneous form evaluates to the powers of the signed constant coefficient of the
characteristic polynomial. We construct one linear factor for each characteristic root,
counting multiplicities.
-/

namespace MetaMathlibExt

namespace exists_homogeneous_form_eval_eq_pow_of_linearRecurrence

variable (E : LinearRecurrence ℂ)

private def bilateral : Submodule ℂ (ℤ → ℂ) where
  carrier := {u | ∀ n : ℤ, u (n + E.order) = ∑ i, E.coeffs i * u (n + (i : ℕ))}
  zero_mem' := by simp
  add_mem' {u v} hu hv n := by
    simp [hu n, hv n, mul_add, Finset.sum_add_distrib]
  smul_mem' a u hu n := by
    simp [hu n, Finset.mul_sum, mul_left_comm]

private def tail (n : ℤ) : bilateral E →ₗ[ℂ] E.solSpace where
  toFun u := ⟨fun t ↦ u.val (n + t), fun t ↦ by simpa [add_assoc] using u.prop (n + t)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def shift : Module.End ℂ E.solSpace where
  toFun u := ⟨fun t ↦ u.val (1 + t), fun t ↦ by simpa [add_assoc] using u.prop (1 + t)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_pow_tail (u : bilateral E) (n : ℤ) (k : ℕ) :
    (shift E ^ k) (tail E n u) = tail E (n + k) u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    ext t
    change u.val (n + k + ↑(1 + t)) = u.val (n + ↑(k + 1) + t)
    exact congrArg u.val (by push_cast; omega)

-- An arbitrarily long past puts each tail in the stable range of the one-sided shift.
-- Consequently a bilateral solution is determined by its nonnegative terms even before
-- we know that the constant coefficient is nonzero.
private theorem ker_tail : (tail E 0).ker = ⊥ := by
  let := Module.Finite.of_basis E.basis
  let d := Module.finrank ℂ E.solSpace
  apply LinearMap.ker_eq_bot'.2
  intro u hu
  ext n
  by_cases hn : 0 ≤ n
  · simpa [tail, Int.toNat_of_nonneg hn] using congrArg (fun v : E.solSpace ↦ v.val n.toNat) hu
  · let m := (-n).toNat
    have hm : (m : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hk : tail E (n - d) u ∈ (shift E ^ (d + m)).ker := by
      rw [LinearMap.mem_ker, shift_pow_tail, Nat.cast_add, hm]
      rwa [show n - ↑d + (↑d + -n) = 0 by omega]
    have hz := Module.End.ker_pow_le_ker_pow_finrank (shift E) (d + m) hk
    change (shift E ^ d) (tail E (n - d) u) = 0 at hz
    rw [shift_pow_tail, sub_add_cancel] at hz
    simpa [tail] using congrArg (fun v : E.solSpace ↦ v.val 0) hz

-- In the basis of the given solutions, a geometric sequence gives a linear form.
private theorem root_linearForm (g : Fin E.order → bilateral E)
    (hind : LinearIndependent ℂ g) {r : ℂ} (hr : E.charPoly.IsRoot r) :
    ∃ L : MvPolynomial (Fin E.order) ℂ, L.IsHomogeneous 1 ∧
      ∀ n : ℤ, MvPolynomial.eval (fun j ↦ (g j).val n) L = r ^ n := by
  classical
  let := Module.Finite.of_basis E.basis
  let B := basisOfLinearIndependentOfCardEqFinrank' _ (hind.map' _ (ker_tail E))
    (Module.finrank_eq_card_basis E.basis).symm
  let v : E.solSpace := ⟨fun t ↦ r ^ t, (E.geom_sol_iff_root_charPoly r).2 hr⟩
  let c := B.repr v
  let u : bilateral E := ∑ j, c j • g j
  have hu : tail E 0 u = v := by
    simpa [u, c, B, Function.comp_def] using B.sum_repr v
  have hnat (t : ℕ) : u.val t = r ^ t := by
    simpa [tail, v] using congrArg (fun w : E.solSpace ↦ w.val t) hu
  let u' : bilateral E := ⟨fun n ↦ u.val (1 + n), fun n ↦ by
    simpa [add_assoc] using u.prop (1 + n)⟩
  have hstep : u' = r • u := by
    apply LinearMap.ker_eq_bot.1 (ker_tail E)
    ext t
    change u.val (1 + (0 + (t : ℤ))) = r * u.val (0 + (t : ℤ))
    simpa [pow_succ', hnat, add_comm (1 : ℤ)] using hnat (t + 1)
  have step (n : ℤ) : u.val (n + 1) = u.val n * r := by
    simpa [u', add_comm, mul_comm] using congrArg (fun w : bilateral E ↦ w.val n) hstep
  have hzero : u.val 0 = 1 := by simpa using hnat 0
  have hr₀ : r ≠ 0 := by
    intro hr₀
    simpa [hr₀, hzero] using step (-1)
  have hpow (n : ℤ) : u.val n = r ^ n := by
    induction n using Int.induction_on with
    | zero => simpa using hzero
    | succ n ih => rw [step, ih, zpow_add_one₀ hr₀]
    | pred n ih =>
      apply mul_right_cancel₀ hr₀
      rw [← step, ← zpow_add_one₀ hr₀, sub_add_cancel, ih]
  refine ⟨∑ j, MvPolynomial.C (c j) * MvPolynomial.X j, ?_, fun n ↦ ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ ↦
      MvPolynomial.isHomogeneous_C_mul_X _ _
  · simpa [u, Submodule.coe_sum, Finset.sum_apply] using hpow n

private theorem form_of_roots (g : Fin E.order → bilateral E) (hind : LinearIndependent ℂ g)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, E.charPoly.IsRoot r) :
    ∃ F : MvPolynomial (Fin E.order) ℂ, F.IsHomogeneous s.card ∧
      ∀ n : ℤ, MvPolynomial.eval (fun j ↦ (g j).val n) F = s.prod ^ n := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, MvPolynomial.isHomogeneous_one _ _, by simp⟩
  | cons r s ih =>
    obtain ⟨L, hL, hevalL⟩ := root_linearForm E g hind (hs r (by simp))
    obtain ⟨F, hF, hevalF⟩ := ih fun a ha ↦ hs a (Multiset.mem_cons_of_mem ha)
    exact ⟨L * F, by simpa [add_comm] using hL.mul hF,
      fun n ↦ by simp [hevalL, hevalF, mul_zpow]⟩

end exists_homogeneous_form_eval_eq_pow_of_linearRecurrence

open exists_homogeneous_form_eval_eq_pow_of_linearRecurrence

/-- **Homogeneous forms taking the values of a power on recurrence sequences.** Let
$\gamma_0, \dots, \gamma_{k-1} \in \mathbb{C}$ and let $\chi(x) = x^k - \sum_{i<k} \gamma_i x^i$
be the characteristic polynomial of the recurrence $G_{n+k} = \sum_{i<k} \gamma_i G_{n+i}$. Let
$G^{(1)}, \dots, G^{(k)} \colon \mathbb{Z} \to \mathbb{C}$ be $\mathbb{C}$-linearly independent
sequences, each satisfying this recurrence for every $n \in \mathbb{Z}$. Then there is a
homogeneous polynomial $F$ of degree $k$ in $k$ variables with complex coefficients such that
$F(G^{(1)}_n, \dots, G^{(k)}_n) = ((-1)^k \chi(0))^n$ for every $n \in \mathbb{Z}$.

For $k \ge 1$ we have $\chi(0) = -\gamma_0$, so the right side is $((-1)^{k+1} \gamma_0)^n$.
The source also assumes $\gamma_0 \neq 0$; for $\mathbb{Z}$-indexed solutions, linear
independence already forces it.

Source: Kálmán Győry, Attila Pethő and László Szalay, *Decomposable Forms Generated by
Linear Recurrences*, Journal of Integer Sequences 27 (2024), Article 24.3.5, Theorem 1
(`jis-2024-24.3.5-thm-1`). -/
public theorem exists_homogeneous_form_eval_eq_pow_of_linearRecurrence
    (E : LinearRecurrence ℂ) (G : Fin E.order → ℤ → ℂ)
    (hG : ∀ j (n : ℤ), G j (n + E.order) = ∑ i, E.coeffs i * G j (n + (i : ℕ)))
    (hind : LinearIndependent ℂ G) :
    ∃ F : MvPolynomial (Fin E.order) ℂ, F.IsHomogeneous E.order ∧
      ∀ n : ℤ, MvPolynomial.eval (fun j => G j n) F =
        ((-1) ^ E.order * E.charPoly.coeff 0) ^ n := by
  let g (j) : bilateral E := ⟨G j, hG j⟩
  have hi : LinearIndependent ℂ g := LinearIndependent.of_comp (bilateral E).subtype hind
  obtain ⟨F, hF, heval⟩ := form_of_roots E g hi E.charPoly.roots
    (fun _ hr ↦ Polynomial.isRoot_of_mem_roots hr)
  have hd := Polynomial.natDegree_eq_of_degree_eq_some (E.charPoly_degree_eq_order)
  have hs := IsAlgClosed.splits E.charPoly
  refine ⟨F, by rwa [← hs.natDegree_eq_card_roots, hd] at hF, ?_⟩
  intro n
  rw [hs.coeff_zero_eq_prod_roots_of_monic E.charPoly_monic, hd, ← mul_assoc, ← mul_pow]
  simpa using heval n

end MetaMathlibExt
