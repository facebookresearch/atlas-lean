/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Scottish Book Problem 62

`ScottishBookProblem62Claim` is the claim of Problem 62 of the Scottish Book, for abelian groups:
if an abelian group `G` is the union of an increasing sequence of subgroups
`H 0 ≤ H 1 ≤ H 2 ≤ ⋯`, each isomorphic to `H 1`, then `G` is isomorphic to `H 1`.
`mazurUlam62_refuted` proves it false with R. Baer's counterexample: `ℚ` is the union of the
increasing subgroups `(1 / n!) ℤ`, each isomorphic to `ℤ`, but `ℚ` is not cyclic, so it is not
isomorphic to `ℤ`.

## Main statements

* `mazurUlam62_refuted`: the claim of Scottish Book Problem 62 is false.
* `mem_zmultiples_inv_natCast_iff`: for `N ≠ 0`, a rational number lies in `(1 / N) ℤ` exactly
  when its denominator divides `N`.
* `monotone_zmultiples_inv_factorial` and `iSup_zmultiples_inv_factorial`: the subgroups
  `(1 / n!) ℤ` of `ℚ` increase with `n`, and their union is `ℚ`.
* `isEmpty_rat_addEquiv`: `ℚ` is isomorphic to no cyclic group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook62Wanted

/-- **Claim of Scottish Book Problem 62.** The claim that for every abelian group $G$ and
every sequence of subgroups $H_0 \le H_1 \le H_2 \le \cdots$ of $G$ whose union is $G$ and
each of which is isomorphic to $H_1$, the group $G$ is itself isomorphic to $H_1$.

The problem is posed for groups; the claim here is restricted to abelian groups, which loses
nothing for its refutation since Baer's counterexample is abelian. -/
def ScottishBookProblem62Claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] (H : ℕ → AddSubgroup G),
    (∀ n, H n ≤ H (n + 1)) →
    (∀ n, Nonempty (↥(H n) ≃+ ↥(H 1))) →
    (⨆ n, H n) = ⊤ →
    Nonempty (G ≃+ ↥(H 1))

open scoped Nat
open AddSubgroup

/-- For `N ≠ 0`, a rational number lies in the subgroup `(1 / N) ℤ` of `ℚ` exactly when its
denominator divides `N`. -/
theorem mem_zmultiples_inv_natCast_iff {N : ℕ} (hN : N ≠ 0) {x : ℚ} :
    x ∈ zmultiples ((N : ℚ)⁻¹) ↔ x.den ∣ N := by
  rw [mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h := Rat.den_dvd k N
    rw [Rat.divInt_eq_div, Int.cast_natCast, div_eq_mul_inv, ← zsmul_eq_mul] at h
    exact Int.natCast_dvd_natCast.1 h
  · rintro ⟨m, rfl⟩
    have hm : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)
    refine ⟨x.num * m, ?_⟩
    conv_rhs => rw [← Rat.num_div_den x]
    rw [zsmul_eq_mul]
    push_cast
    field_simp

/-- The subgroups `(1 / n!) ℤ` of `ℚ` increase with `n`. -/
theorem monotone_zmultiples_inv_factorial : Monotone fun n : ℕ ↦ zmultiples ((n ! : ℚ)⁻¹) :=
  fun m n hmn _ hx ↦ (mem_zmultiples_inv_natCast_iff n.factorial_ne_zero).2 <|
    ((mem_zmultiples_inv_natCast_iff m.factorial_ne_zero).1 hx).trans
      (Nat.factorial_dvd_factorial hmn)

/-- The supremum of the subgroups `(1 / n!) ℤ` of `ℚ` is `ℚ`: a rational number with denominator
`q` lies in `(1 / q!) ℤ`, so their union is already `ℚ`. -/
theorem iSup_zmultiples_inv_factorial : ⨆ n : ℕ, zmultiples ((n ! : ℚ)⁻¹) = ⊤ :=
  (eq_top_iff' _).2 fun x ↦ mem_iSup_of_mem x.den <|
    (mem_zmultiples_inv_natCast_iff x.den.factorial_ne_zero).2
      (Nat.dvd_factorial x.den_pos le_rfl)

/-- The additive group `ℚ` is isomorphic to no cyclic group, since it is not cyclic. -/
theorem isEmpty_rat_addEquiv {G : Type*} [AddGroup G] [IsAddCyclic G] : IsEmpty (ℚ ≃+ G) :=
  ⟨fun e ↦ not_isAddCyclic_of_denselyOrdered ℚ
    (isAddCyclic_of_surjective e.symm e.symm.surjective)⟩

/--
**Refutation of Scottish Book Problem 62.** The claim of Scottish Book Problem 62 is false:
there are an abelian group $G$ and subgroups $H_0 \le H_1 \le H_2 \le \cdots$ of $G$ whose
union is $G$, each isomorphic to $H_1$, such that $G$ is not isomorphic to $H_1$.

R. Baer's counterexample is $G = \mathbb{Q}$ with $H_n = \frac{1}{n!}\mathbb{Z}$: each $H_n$
is isomorphic to $\mathbb{Z}$ and their union is $\mathbb{Q}$, but $\mathbb{Q}$ is not
isomorphic to $\mathbb{Z}$.

Source: S. Mazur and
S. Ulam, Problem 62 of the Scottish Book; the typescript Ad 62 records
R. Baer's remark giving the counterexample, with `G` the group of
rational numbers and `G 1` the integers: the rationals are the union of
an increasing chain of subgroups each isomorphic to the integers (for
example the subgroups `(1 / n !) ℤ`), but the rationals are not
isomorphic to the integers.
-/
theorem mazurUlam62_refuted : ¬ ScottishBookProblem62Claim := by
  intro h
  have hne (n : ℕ) : (n ! : ℚ)⁻¹ ≠ 0 := inv_ne_zero (mod_cast n.factorial_ne_zero)
  obtain ⟨e⟩ := h ℚ (fun n ↦ zmultiples ((n ! : ℚ)⁻¹))
    (fun n ↦ monotone_zmultiples_inv_factorial n.le_succ)
    (fun n ↦ ⟨(zmultiplesEquivInt (hne n)).trans (zmultiplesEquivInt (hne 1)).symm⟩)
    iSup_zmultiples_inv_factorial
  exact isEmpty_rat_addEquiv.elim (e.trans (zmultiplesEquivInt (hne 1)))

end MathlibExt.GroupTheory.ScottishBook62Wanted
