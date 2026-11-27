/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Arithmetic progressions in CR-sets

If `A` is a combinatorially rich subset of an additive commutative semigroup `S`, then for
any `l : ℕ` the pairs `(a, b)` whose progression from `a` through `a + l b` lies in `A` form
a combinatorially rich subset of `S × S`. Iterated addition handles the case where `S`
has no zero.

## References

* Dibyendu De and Pintu Debnath, *Abundance of Arithmetic Progressions in CR-Sets*,
  INTEGERS 25 (2025), Article A4, pp. 1–8, Definition 2 (§1) and Theorem 8 (§3).
* Vitaly Bergelson and Daniel Glasscock, *On the interplay between notions of additive
  and multiplicative largeness and its combinatorial applications*, Journal of
  Combinatorial Theory, Series A 172 (2020), Article 105203, §2, for the original notion
  of combinatorial richness, as credited by De and Debnath.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **CR-set.** A subset $A$ of a commutative semigroup $(S, +)$ is a CR-set (combinatorially rich)
when for every natural number $n$, including $n = 0$, there is a natural number $r$ such that for
every $r \times n$ matrix $(m_{ij})$ with entries in $S$ there are a nonempty set
$\alpha \subseteq \{1, \ldots, r\}$ and an element $s \in S$ such that
$s + \sum_{i \in \alpha} m_{ij} \in A$ for every column $j \in \{1, \ldots, n\}$.

The paper takes $n \ge 1$. Allowing $n = 0$ adds the requirement that $S$ be nonempty, the
paper's implicit convention: over an empty $S$ every case $n \ge 1$ holds vacuously (take
$r = 1$; there is no matrix), so without it $\emptyset$ would be a CR-set of the empty
semigroup. Over a nonempty $S$ the two definitions agree.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
def IsCRSet {S : Type*} [AddCommSemigroup S] (A : Set S) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, ∀ M : Fin r → Fin n → S, ∃ α : Finset (Fin r), α.Nonempty ∧
    ∃ s : S, ∀ j, (α.toList.map fun i => M i j).foldl (· + ·) s ∈ A

/-- **Arithmetic progressions in CR-sets.** If $A$ is a CR-set in a commutative semigroup
$(S, +)$ and $l$ is a natural number, then the set of pairs $(a, b) \in S \times S$ such that
$a, a + b, a + 2b, \dots, a + lb$ all lie in $A$ is a CR-set in $S \times S$. Here $a + ib$ is
$a$ followed by $i$ additions of $b$, since $S$ need not have a zero.

The paper takes $l \ge 1$; the case $l = 0$ is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 8 (`integers-2025-A4-thm-8`). -/
public theorem IsCRSet.arithmeticProgressions {S : Type*} [AddCommSemigroup S]
    {A : Set S} (hA : IsCRSet A) (l : ℕ) :
    IsCRSet {p : S × S | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A} := by
  obtain ⟨_, hr₀⟩ := hA 0
  obtain ⟨_, _, t, _⟩ := hr₀ fun _ => Fin.elim0
  intro n
  obtain ⟨r, hr⟩ := hA (n * (l + 1))
  refine ⟨r, fun M => ?_⟩
  let eval (i : ℕ) (p : S × S) : S := (· + p.2)^[i] p.1
  let shift (b : S) (p : S × S) : S × S := (p.1, b + p.2)
  have eval_add (i : ℕ) (p q : S × S) : eval i (p + q) = eval i p + eval i q := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [eval, Function.iterate_succ_apply', Prod.snd_add] at ih ⊢
      rw [ih, add_add_add_comm]
  let e : Fin n × Fin (l + 1) ≃ Fin (n * (l + 1)) := finProdFinEquiv
  obtain ⟨α, hα, s, hs⟩ := hr fun k c => eval (e.symm c).2 (shift t (M k (e.symm c).1))
  -- Each selected row adds one copy of `t` to the common second-coordinate shift.
  cases hrows : α.toList with
  | nil => exact (hα.toList_ne_nil hrows).elim
  | cons k₀ rows =>
    let d := rows.foldl (fun b _ => b + t) t
    refine ⟨α, hα, (s, d), fun j i hi => ?_⟩
    let step (p : S × S) (k : Fin r) := p + M k j
    let p₀ : S × S := (s + (M k₀ j).1, (M k₀ j).2)
    have hshift (p : S × S) (k : Fin r) : step (shift d p) k = shift d (step p k) :=
      Prod.ext rfl (add_assoc d p.2 (M k j).2)
    have hstart : s + eval i (shift t (M k₀ j)) = eval i (shift t p₀) := by
      have hc : Function.Commute (s + ·) (· + (shift t (M k₀ j)).2) :=
        fun x => (add_assoc s x _).symm
      exact hc.iterate_right i _
    have hfold := List.foldl_hom₂ rows (fun p b => eval i (shift b p)) step
      (fun b _ => b + t) (fun a k => a + eval i (shift t (M k j))) p₀ t (fun p b k => by
        rw [← eval_add]
        exact congrArg (eval i) (Prod.ext rfl (add_add_add_comm b t p.2 (M k j).2)))
    have hcol := hs (e (j, ⟨i, Nat.lt_succ_of_le hi⟩))
    simp only [Equiv.symm_apply_apply, hrows, List.foldl_map, List.foldl_cons] at hcol
    change rows.foldl (fun a k => a + eval i (shift t (M k j)))
      (s + eval i (shift t (M k₀ j))) ∈ A at hcol
    rw [hstart, hfold] at hcol
    simp only [hrows, List.foldl_map, List.foldl_cons]
    change eval i (rows.foldl step (shift d p₀)) ∈ A
    rw [List.foldl_hom (shift d) hshift]
    exact hcol

end

end MetaMathlibExt
