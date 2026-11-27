/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

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

private theorem eq_of_agree_on_support (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool)
    (hxy : ∀ i ∈ essentialSupport f, x i = y i) : f x = f y := by
  classical
  -- Replace the coordinates outside the support one at a time.
  have hreplace (s : Finset (Fin n)) (hs : ∀ i ∈ s, ¬ IsBoolFunNondegenerateOn f i) :
      f (s.piecewise x y) = f y := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [piecewise_insert, ← ih (fun j hj => hs j (mem_insert_of_mem hj))]
      rcases Bool.eq_or_eq_not (x i) (s.piecewise x y i) with h | h
      · simp only [h, update_eq_self]
      · rw [h]
        exact (not_ne_iff.mp fun hn => hs i (mem_insert_self ..) ⟨_, hn⟩).symm
  have h := hreplace (essentialSupport f)ᶜ fun i hi hnd =>
    (mem_compl.mp hi) ((mem_essentialSupport f i).2 hnd)
  have heq : (essentialSupport f)ᶜ.piecewise x y = x := by
    funext i
    by_cases hi : i ∈ essentialSupport f
    · simp [hi, hxy i hi]
    · simp [hi]
  rwa [heq] at h

private theorem card_support_fiber (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (s : Finset (Fin n)) :
    Nat.card {f : {f : (Fin n → Bool) → Bool // P n f} // essentialSupport f.val = s} =
      Nat.card {g : (Fin s.card → Bool) → Bool // IsNondegenerateBoolFun g ∧ P s.card g} := by
  classical
  let e : Fin s.card ↪ Fin n := (s.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range e = (s : Set (Fin n)) := s.range_orderEmbOfFin rfl
  have hmap : univ.map e = s := by
    ext i
    simpa [Set.mem_range] using Set.ext_iff.mp hrange i
  have hlift (g : (Fin s.card → Bool) → Bool) :
      essentialSupport (fun x => g (x ∘ e)) = s ↔ IsNondegenerateBoolFun g := by
    rw [essentialSupport_lift]
    calc
      (essentialSupport g).map e = s ↔ (essentialSupport g).map e = univ.map e :=
        ⟨fun h => h.trans hmap.symm, fun h => h.trans hmap⟩
      _ ↔ IsNondegenerateBoolFun g := by
        simp [map_inj, eq_univ_iff_forall, mem_essentialSupport, IsNondegenerateBoolFun]
  let extendInput (y : Fin s.card → Bool) : Fin n → Bool := Function.extend e y (fun _ => false)
  have hrestrict (y : Fin s.card → Bool) : extendInput y ∘ e = y :=
    funext fun i => e.injective.extend_apply y (fun _ => false) i
  let lift (g : {g : (Fin s.card → Bool) → Bool // IsNondegenerateBoolFun g ∧ P s.card g}) :
      {f : {f : (Fin n → Bool) → Bool // P n f} // essentialSupport f.val = s} :=
    ⟨⟨fun x => g.val (x ∘ e), (hP _ _ e g.val).2 g.property.2⟩, (hlift g.val).2 g.property.1⟩
  symm
  apply Nat.card_eq_of_bijective lift
  constructor
  · intro g g' hg
    apply Subtype.ext
    funext y
    have heq := congrArg (fun f => f.val.val (extendInput y)) hg
    simpa only [lift, hrestrict] using heq
  · rintro ⟨⟨f, hf⟩, hs⟩
    have hrecover : (fun x => (f ∘ extendInput) (x ∘ e)) = f := by
      funext x
      apply eq_of_agree_on_support f (extendInput (x ∘ e)) x
      intro i hi
      have hir : i ∈ Set.range e := by simpa only [hrange, mem_coe, ← hs] using hi
      obtain ⟨j, rfl⟩ := hir
      exact congrFun (hrestrict (x ∘ e)) j
    have hs' := (congrArg essentialSupport hrecover).trans hs
    refine ⟨⟨f ∘ extendInput, (hlift _).1 hs', (hP _ _ e _).1 ?_⟩, ?_⟩
    · rwa [hrecover]
    · exact Subtype.ext (Subtype.ext hrecover)

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
