/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean
import all MathlibExt.Combinatorics.Enumerative.BooleanFunctionInclusionExclusion
import Mathlib.Data.Fintype.Powerset

/-!
# Counting Boolean functions by essential support

The essential support is the set of variables on which a Boolean function depends.
For a fixed support, restricting to those variables gives a bijection with non-degenerate
functions on that many variables. The predicate must be invariant under adding dummy variables;
this hypothesis is explicit here but not stated in Proposition 1.

## References

* Aniruddha Biswas and Palash Sarkar, *Counting Unate and Monotone Boolean Functions Under
  Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025),
  Article 25.3.4, pp. 1–19, Proposition 1, equation (2), p. 5.
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Biswas/biswas6.pdf>
* Ringo Baumann and Hannes Straß, *On the Number of Bipolar Boolean Functions*, Journal of Logic
  and Computation 27 (2017), no. 8, pp. 2431–2449, Proposition 10 and Corollary 11, give the
  monotone special case credited in Remark 2 of Biswas and Sarkar.
-/

namespace MetaMathlibExt

open Finset Function

variable {m n : ℕ}

private noncomputable def essentialSupport (f : (Fin n → Bool) → Bool) : Finset (Fin n) := by
  classical
  exact univ.filter (IsBoolFunNondegenerateOn f)

private theorem mem_essentialSupport (f : (Fin n → Bool) → Bool) (i : Fin n) :
    i ∈ essentialSupport f ↔ IsBoolFunNondegenerateOn f i := by
  classical
  simp [essentialSupport]

private theorem essentialSupport_lift (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool) :
    essentialSupport (fun x => g (x ∘ e)) = (essentialSupport g).map e := by
  classical
  ext i
  simp only [mem_essentialSupport, mem_map]
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    simp only [e.injective.eq_iff, exists_eq_right, IsBoolFunNondegenerateOn,
      update_comp_eq_of_injective _ e.injective]
    have hsurj : Surjective (fun x : Fin n → Bool => x ∘ e) :=
      e.injective.surjective_comp_right
    exact (hsurj.exists (p := fun x => g x ≠ g (update x j (!x j)))).symm
  · have hne (j : Fin m) : e j ≠ i := fun h => hi ⟨j, h⟩
    simp [IsBoolFunNondegenerateOn, update_comp_eq_of_forall_ne _ _ hne, hne]

open card_nondegenerate_boolFun_eq_alternating_sum (card_ignoring) in
private theorem card_support_fiber (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (s : Finset (Fin n)) :
    Nat.card {f : {f : (Fin n → Bool) → Bool // P n f} // essentialSupport f.val = s} =
      Nat.card {g : (Fin s.card → Bool) → Bool // IsNondegenerateBoolFun g ∧ P s.card g} := by
  classical
  -- Specifying the support size is invariant under adding dummy variables, so the same
  -- restriction count applies to functions of property `P` with exactly `s.card` essential inputs.
  let Q (k : ℕ) (f : (Fin k → Bool) → Bool) := P k f ∧ (essentialSupport f).card = s.card
  have hQ (m k : ℕ) (e : Fin m ↪ Fin k) (g : (Fin m → Bool) → Bool) :
      Q k (fun x => g (x ∘ e)) ↔ Q m g := by
    simp only [Q, essentialSupport_lift, card_map, hP]
  have hs (f : (Fin n → Bool) → Bool) :
      essentialSupport f = s ↔ (essentialSupport f).card = s.card ∧
        ∀ i ∈ sᶜ, ¬ IsBoolFunNondegenerateOn f i := by
    constructor
    · intro h
      refine ⟨congrArg Finset.card h, fun i hi hnd => ?_⟩
      exact (mem_compl.mp hi) (h ▸ (mem_essentialSupport f i).2 hnd)
    · rintro ⟨hcard, hignore⟩
      refine eq_of_subset_of_card_le ?_ hcard.ge
      intro i hi
      by_contra his
      exact hignore i (mem_compl.mpr his) ((mem_essentialSupport f i).1 hi)
  have harity : n - sᶜ.card = s.card := by
    rw [card_compl, Fintype.card_fin]
    exact Nat.sub_sub_self (s.card_le_univ.trans_eq (Fintype.card_fin n))
  calc
    _ = Nat.card {f : {f : (Fin n → Bool) → Bool // Q n f} //
          ∀ i ∈ sᶜ, ¬ IsBoolFunNondegenerateOn f.val i} := by
      apply Nat.card_congr
      refine (Equiv.subtypeSubtypeEquivSubtypeInter (P n) (fun f => essentialSupport f = s)).trans
        ((Equiv.subtypeEquivRight fun f => ?_).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (Q n) (fun f =>
            ∀ i ∈ sᶜ, ¬ IsBoolFunNondegenerateOn f i)).symm)
      simp only [Q, hs f, and_assoc]
    _ = Nat.card {f : (Fin s.card → Bool) → Bool // Q s.card f} :=
      (card_ignoring Q hQ sᶜ).trans
        (congrArg (fun k => Nat.card {f : (Fin k → Bool) → Bool // Q k f}) harity)
    _ = _ := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun g => ?_
      have hfull : (essentialSupport g).card = s.card ↔ IsNondegenerateBoolFun g := by
        simpa only [Fintype.card_fin, eq_univ_iff_forall, mem_essentialSupport,
          IsNondegenerateBoolFun] using (card_eq_iff_eq_univ (essentialSupport g))
      exact and_comm.trans (and_congr hfull Iff.rfl)

/-- **Counting Boolean functions by their non-degenerate restrictions.** Let $P$ be a property
of Boolean functions on any number of variables that is invariant under renaming variables
along injections: for all $m, n$, every injective map $e$ from $\{1, \dots, m\}$ to
$\{1, \dots, n\}$ and every $m$-variable function $g$, the $n$-variable function
$x \mapsto g(x_{e(1)}, \dots, x_{e(m)})$ has $P$ if and only if $g$ has $P$. Write $P_n$ for the
number of $n$-variable Boolean functions with $P$ and $\mathrm{nd}\text{-}P_i$ for the number of
non-degenerate $i$-variable Boolean functions with $P$. Then for every $n \ge 0$,

$$P_n = \sum_{i=0}^{n} \binom{n}{i} \, \mathrm{nd}\text{-}P_i.$$

The invariance hypothesis cannot be dropped: if $P$ holds exactly for the four $1$-variable
functions, then $P_1 = 4$ but the right-hand side is $0 + 2 = 2$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 1 (`jis-2025-25.3.4-prop-1`). -/
public theorem card_boolFun_eq_sum_choose_card_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // P n f}
      = ∑ i ∈ Finset.range (n + 1),
          n.choose i * Nat.card {f : (Fin i → Bool) → Bool // IsNondegenerateBoolFun f ∧ P i f}
    := by
  classical
  let support (f : {f : (Fin n → Bool) → Bool // P n f}) := essentialSupport f.val
  let count (i : ℕ) := Nat.card {f : (Fin i → Bool) → Bool // IsNondegenerateBoolFun f ∧ P i f}
  calc
    _ = Nat.card (Σ s, {f // support f = s}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv support).symm
    _ = ∑ s : Finset (Fin n), count s.card := by
      rw [Nat.card_sigma]
      exact sum_congr rfl fun s _ => card_support_fiber P hP s
    _ = _ := by
      rw [← powerset_univ, sum_powerset_apply_card count]
      simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, count]

end MetaMathlibExt
