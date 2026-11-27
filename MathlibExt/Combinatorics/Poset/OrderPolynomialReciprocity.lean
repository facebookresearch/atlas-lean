/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Poset.OrderPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Order.Minimal

/-!
# Reciprocity for order polynomials

The signed evaluations of the order polynomial at negative integers count strictly monotone maps.
We obtain the shift identity for the polynomial by inclusion-exclusion on the minimal elements.
-/

public section

open Finset Polynomial MathlibExt.Combinatorics.Poset.OrderPolynomial

namespace MathlibExt.Combinatorics.Poset.OrderPolynomialWanted

variable {P : Type*} [PartialOrder P]

private abbrev WeakMaps (P : Type*) [PartialOrder P] (m : ℕ) :=
  {f : P → Fin m // Monotone f}

private abbrev StrictMaps (P : Type*) [PartialOrder P] (m : ℕ) :=
  {f : P → Fin m // StrictMono f}

open Classical in
private noncomputable def minima (P : Type*) [PartialOrder P] [Fintype P] : Finset P :=
  univ.filter IsMin

variable [Fintype P]

private lemma minimal_of_mem {S : Finset P} (hS : S ⊆ minima P) {x : P} (hx : x ∈ S) :
    IsMin x := by
  classical
  exact (mem_filter.mp (hS hx)).2

open Classical in
/-- Restriction removes the minimal elements on which a weak map is required to be zero. -/
private noncomputable def weakZeroEquiv {m : ℕ} (S : Finset P) (hS : S ⊆ minima P) :
    {f : WeakMaps P (m + 1) // ∀ x ∈ S, f.1 x = 0} ≃ WeakMaps {x // x ∉ S} (m + 1) where
  toFun f := ⟨fun x => f.1.1 x, fun _ _ h => f.1.2 h⟩
  invFun g := ⟨⟨fun x => if h : x ∈ S then 0 else g.1 ⟨x, h⟩, by
    intro x y hxy
    by_cases hx : x ∈ S
    · simp [hx]
    · have hy : y ∉ S := fun hy => hx ((minimal_of_mem hS hy).eq_of_le hxy ▸ hy)
      simpa only [dite_eq_right hx, dite_eq_right hy] using
        g.2 (show (⟨x, hx⟩ : {x // x ∉ S}) ≤ ⟨y, hy⟩ from hxy)⟩,
    fun x hx => dite_eq_left hx⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S <;> simp [hx, f.2]
  right_inv g := by
    apply Subtype.ext
    funext x
    simp [x.2]

/-- A weak map that is positive on the minima is positive everywhere, so we may subtract one. -/
private noncomputable def positiveEquiv (m : ℕ) :
    {f : WeakMaps P (m + 1) // ∀ x ∈ minima P, f.1 x ≠ 0} ≃ WeakMaps P m := by
  classical
  have positive (f : WeakMaps P (m + 1)) (hf : ∀ x ∈ minima P, f.1 x ≠ 0) (x : P) :
      f.1 x ≠ 0 := by
    obtain ⟨y, hyx, hy⟩ :=
      exists_minimal_le_of_wellFoundedLT (fun _ => True) x trivial
    have hy' : y ∈ minima P := mem_filter.mpr ⟨mem_univ _, minimal_true.mp hy⟩
    exact ne_of_gt ((Fin.pos_iff_ne_zero.mpr (hf y hy')).trans_le (f.2 hyx))
  exact
    { toFun := fun f => ⟨fun x => (f.1.1 x).pred (positive f.1 f.2 x), by
        intro x y hxy
        rw [← Fin.succ_le_succ_iff, Fin.succ_pred, Fin.succ_pred]
        exact f.1.2 hxy⟩
      invFun := fun g => ⟨⟨fun x => (g.1 x).succ, fun _ _ h => Fin.succ_le_succ_iff.mpr (g.2 h)⟩,
        fun _ _ => Fin.succ_ne_zero _⟩
      left_inv := fun f =>
        Subtype.ext (Subtype.ext (funext fun x => Fin.succ_pred _ (positive f.1 f.2 x)))
      right_inv := fun g =>
        Subtype.ext (funext fun x => Fin.pred_succ (h := Fin.succ_ne_zero _) _) }

private lemma mem_inf_sets {α ι : Type*} [DecidableEq α] [Fintype α] (a : α) (s : Finset ι)
    (A : ι → Finset α) : a ∈ s.inf A ↔ ∀ i ∈ s, a ∈ A i := by
  simpa only [singleton_subset_iff] using
    (Finset.le_inf_iff (a := ({a} : Finset α)) (s := s) (f := A))

private lemma weak_shift (m : ℕ) :
    (orderPolynomialValue P m : ℚ) = ∑ S ∈ (minima P).powerset,
      (-1 : ℚ) ^ S.card * orderPolynomialValue {x // x ∉ S} (m + 1) := by
  classical
  let A (x : P) := univ.filter (fun f : WeakMaps P (m + 1) => f.1 x = 0)
  have hpos : ((minima P).inf fun x => (A x)ᶜ).card = orderPolynomialValue P m := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    refine (Equiv.subtypeEquivRight fun f => ?_).trans (positiveEquiv m)
    rw [mem_inf_sets]
    simp [A]
  have hzero (S : Finset P) (hS : S ∈ (minima P).powerset) :
      (S.inf A).card = orderPolynomialValue {x // x ∉ S} (m + 1) := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    refine (Equiv.subtypeEquivRight fun f => ?_).trans (weakZeroEquiv S (mem_powerset.mp hS))
    rw [mem_inf_sets]
    simp [A]
  have h := inclusion_exclusion_card_inf_compl (minima P) A
  rw [hpos] at h
  exact_mod_cast h.trans (sum_congr rfl fun S hS => by rw [hzero S hS]; rfl)

private def zeros {m : ℕ} (f : StrictMaps P (m + 1)) : Finset P :=
  univ.filter fun x => f.1 x = 0

private lemma zeros_subset {m : ℕ} (f : StrictMaps P (m + 1)) : zeros f ⊆ minima P := by
  classical
  intro x hx
  have hx' : f.1 x = 0 := (mem_filter.mp hx).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, isMin_iff_forall_not_lt.mpr fun y hy => ?_⟩
  exact (Fin.not_lt_zero _) (hx' ▸ f.2 hy)

/-- In a strict map the zero fiber is a subset of the minima. After fixing it,
subtracting one on its complement gives an arbitrary strict map to the shorter chain. -/
private noncomputable def strictFiberEquiv {m : ℕ} (S : Finset P) (hS : S ⊆ minima P) :
    {f : StrictMaps P (m + 1) // zeros f = S} ≃ StrictMaps {x // x ∉ S} m := by
  classical
  have hfiber (f : {f : StrictMaps P (m + 1) // zeros f = S}) (x : P) :
      x ∈ S ↔ f.1.1 x = 0 :=
    (Finset.ext_iff.mp f.2 x).symm.trans (by simp [zeros])
  let extend (g : StrictMaps {x // x ∉ S} m) (x : P) : Fin (m + 1) :=
    if h : x ∈ S then 0 else (g.1 ⟨x, h⟩).succ
  have hext (g : StrictMaps {x // x ∉ S} m) : StrictMono (extend g) := by
    intro x y hxy
    have hy : y ∉ S := fun hy => (minimal_of_mem hS hy).not_lt hxy
    by_cases hx : x ∈ S
    · simp [extend, hx, hy]
    · simp only [extend, dite_eq_right hx, dite_eq_right hy, Fin.succ_lt_succ_iff]
      exact g.2 (show (⟨x, hx⟩ : {x // x ∉ S}) < ⟨y, hy⟩ from hxy)
  exact
    { toFun := fun f => ⟨fun x => (f.1.1 x).pred ((hfiber f x).not.mp x.2), by
        intro x y hxy
        rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
        exact f.1.2 hxy⟩
      invFun := fun g => ⟨⟨extend g, hext g⟩, by
        ext x
        by_cases hx : x ∈ S <;> simp [zeros, extend, hx]⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ S <;> simp [extend, hx, (hfiber f x).mp, Fin.succ_pred]
      right_inv := fun g => by
        apply Subtype.ext
        funext x
        apply Fin.succ_inj.mp
        simp [extend, x.2] }

private lemma strict_shift (m : ℕ) :
    strictOrderPolynomialValue P (m + 1) =
      ∑ S ∈ (minima P).powerset, strictOrderPolynomialValue {x // x ∉ S} m := by
  classical
  change Nat.card (StrictMaps P (m + 1)) = _
  rw [Nat.card_eq_fintype_card, ← card_univ,
    card_eq_sum_card_fiberwise (f := zeros) (t := (minima P).powerset)
      (fun f _ => mem_powerset.mpr (zeros_subset f))]
  refine sum_congr rfl fun S hS => ?_
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (strictFiberEquiv S (mem_powerset.mp hS))

private noncomputable def weakPoly (P : Type*) [PartialOrder P] [Fintype P] : ℚ[X] :=
  (exists_orderPolynomial P).choose

private lemma eval_weakPoly_nat (m : ℕ) : (weakPoly P).eval (m : ℚ) = orderPolynomialValue P m :=
  (exists_orderPolynomial P).choose_spec.2.2 m

open Classical in
/-- The shift identity extends from natural arguments to all rational arguments. -/
private lemma eval_weakPoly_shift (z : ℚ) :
    (weakPoly P).eval z = ∑ S ∈ (minima P).powerset,
      (-1 : ℚ) ^ S.card * (weakPoly {x // x ∉ S}).eval (z + 1) := by
  let R : ℚ[X] := ∑ S ∈ (minima P).powerset,
    C ((-1 : ℚ) ^ S.card) * (weakPoly {x // x ∉ S}).comp (X + 1)
  have eval_R (x : ℚ) : R.eval x = ∑ S ∈ (minima P).powerset,
      (-1 : ℚ) ^ S.card * (weakPoly {x // x ∉ S}).eval (x + 1) := by
    simp [R, eval_finsetSum]
  have h : weakPoly P = R := by
    apply eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
    rintro _ ⟨m, rfl⟩
    simpa only [Set.mem_ofPred_eq, eval_R, ← Nat.cast_succ, eval_weakPoly_nat] using
      (weak_shift (P := P) m)
  rw [h, eval_R]

private lemma eval_weakPoly_neg (m : ℕ) :
    (-1 : ℚ) ^ Fintype.card P * (weakPoly P).eval (-(m : ℚ)) =
      strictOrderPolynomialValue P m := by
  classical
  induction m generalizing P with
  | zero =>
    rw [show -((0 : ℕ) : ℚ) = ((0 : ℕ) : ℚ) by simp, eval_weakPoly_nat]
    cases isEmpty_or_nonempty P with
    | inl h =>
      have e : WeakMaps P 0 ≃ StrictMaps P 0 :=
        Equiv.subtypeEquivRight fun _ => iff_of_true (fun {x} => isEmptyElim x)
          (fun {x} => isEmptyElim x)
      simpa [orderPolynomialValue, strictOrderPolynomialValue] using Fintype.card_congr e
    | inr h =>
      have : IsEmpty (WeakMaps P 0) := ⟨fun f => Fin.elim0 (f.1 h.some)⟩
      have : IsEmpty (StrictMaps P 0) := ⟨fun f => Fin.elim0 (f.1 h.some)⟩
      simp [orderPolynomialValue, strictOrderPolynomialValue]
  | succ m ih =>
    rw [eval_weakPoly_shift, strict_shift, Nat.cast_sum, Finset.mul_sum]
    have harg : -((m + 1 : ℕ) : ℚ) + 1 = -(m : ℚ) := by push_cast; ring
    rw [harg]
    refine sum_congr rfl fun S _ => ?_
    rw [← mul_assoc, ← ih (P := {x // x ∉ S})]
    congr 1
    have hcard : Fintype.card P = Fintype.card {x // x ∉ S} + S.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
      exact (Nat.sub_add_cancel S.card_le_univ).symm
    rw [hcard, pow_add, mul_assoc, ← mul_pow]
    simp

variable (P)

/-- **Reciprocity theorem for order polynomials.** The polynomial `Ω_P` that counts
order-preserving maps `P → [m]` satisfies `Ω̄_P(m) = (-1)^p Ω_P(-m)`, where `Ω̄_P(m)` counts the
strictly order-preserving maps `P → [m]` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed.,
author's draft of 15 July 2011, Corollary 3.15.12, for a natural labelling `ω`, whose
complementary labelling `ω̄` is dual natural). -/
theorem orderPolynomial_reciprocity :
    ∃ Q : ℚ[X], (∀ m : ℕ, Q.eval (m : ℚ) = orderPolynomialValue P m) ∧
      ∀ m : ℕ, (-1 : ℚ) ^ Fintype.card P * Q.eval (-(m : ℚ)) = strictOrderPolynomialValue P m :=
  ⟨weakPoly P, eval_weakPoly_nat, eval_weakPoly_neg⟩

end MathlibExt.Combinatorics.Poset.OrderPolynomialWanted
