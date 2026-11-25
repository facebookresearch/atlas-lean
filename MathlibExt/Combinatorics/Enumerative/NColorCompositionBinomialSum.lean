/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Sym.NatCard
import Mathlib.Tactic.Ring

/-!
# Binomial sum for compositions with colors 1 and 2

For total size `n + 2`, partition by the first part: remove a leading `(1, 1)` or `(2, 2)`,
or shorten the first part by one if its size exceeds its color. This gives two copies of the
compositions of `n + 1` and one of those of `n`. Pascal's identity gives the same recurrence
for the even-indexed binomial sum. This is an alternative to the endpoint selection proof
of Hopkins and Wang, Theorem 3.

The public definitions and theorem keep their original `NColorCompositionsWanted` namespace.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- **n-color compositions with two allowed consecutive colors.** For natural numbers $b$ and $n$,
$\mathrm{CCo}_{b,b+1}(n)$ is the set of $n$-color compositions of $n$ that use only the colors $b$
and $b+1$: finite sequences of pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural numbers (part
$k_i$ with color $c_i$) such that $1 \le c_i \le k_i$ and $c_i \in \{b, b+1\}$ for every $i$, and
$k_1 + \dots + k_m = n$. -/
def ColorCompAllowed (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ (pc.2 = b ∨ pc.2 = b + 1)) ∧
      (l.map Prod.fst).sum = n }

/-- **Count of n-color compositions with two consecutive colors.** An $n$-color composition of a
natural number $n$ is a finite sequence of parts, each a positive integer $k$ carrying a color
$c$ with $1 \le c \le k$, whose sizes sum to $n$. For natural numbers $b$ and $n$,
$\operatorname{cco}_{b,b+1}(n)$ is the number of $n$-color compositions of $n$ in which every
part has color $b$ or $b+1$. -/
noncomputable def ccoAllowed (b n : ℕ) : ℕ :=
  Nat.card (ColorCompAllowed b n)

private def prepend {n k c m : ℕ} (h : 1 ≤ c ∧ c ≤ k ∧ (c = 1 ∨ c = 2))
    (p : ColorCompAllowed 1 n) (hs : k + n = m) : ColorCompAllowed 1 m :=
  ⟨(k, c) :: p.val, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
    exact ⟨⟨h, p.property.1⟩, (congrArg (k + ·) p.property.2).trans hs⟩⟩

private def grow {n : ℕ} : ColorCompAllowed 1 (n + 1) → ColorCompAllowed 1 (n + 2)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(k, c) :: l, h⟩ => ⟨(k + 1, c) :: l, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h ⊢
    obtain ⟨⟨⟨hcpos, hcle, hcolor⟩, hparts⟩, hsum⟩ := h
    exact ⟨⟨⟨hcpos, by omega, hcolor⟩, hparts⟩, by omega⟩⟩

private def splitLeading {n : ℕ} : ColorCompAllowed 1 (n + 2) →
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(k, c) :: l, h⟩ => by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h
    obtain ⟨⟨⟨hcpos, hcle, hcolor⟩, hparts⟩, hsum⟩ := h
    if hkc : k = c then
      if hc : c = 1 then
        exact .inl ⟨l, hparts, by omega⟩
      else
        exact .inr (.inr ⟨l, hparts, by omega⟩)
    else
      exact .inr (.inl ⟨(k - 1, c) :: l, by
        simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
        exact ⟨⟨⟨hcpos, by omega, hcolor⟩, hparts⟩, by omega⟩⟩)

private def joinLeading {n : ℕ} :
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n) →
      ColorCompAllowed 1 (n + 2)
  | .inl p => prepend (k := 1) (c := 1) (by decide) p (by omega)
  | .inr (.inl p) => grow p
  | .inr (.inr p) => prepend (k := 2) (c := 2) (by decide) p (by omega)

private def leadingEquiv (n : ℕ) : ColorCompAllowed 1 (n + 2) ≃
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n) where
  toFun := splitLeading
  invFun := joinLeading
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      obtain ⟨k, c⟩ := p
      have hp := h.1 (k, c) (by simp)
      change 1 ≤ c ∧ c ≤ k ∧ (c = 1 ∨ c = 2) at hp
      by_cases hkc : k = c
      · rcases hp.2.2 with hc | hc
        · subst k; subst c; rfl
        · subst k; subst c; rfl
      · apply Subtype.ext
        simp [splitLeading, joinLeading, grow, hkc, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  right_inv := by
    rintro (p | p | p)
    · cases p; rfl
    · obtain ⟨l, h⟩ := p
      cases l with
      | nil => exact False.elim (by simpa using h.2)
      | cons p l =>
        obtain ⟨k, c⟩ := p
        have hp := (h.1 (k, c) (by simp)).2.1
        change c ≤ k at hp
        simp [joinLeading, grow, splitLeading, show k + 1 ≠ c by omega]
    · cases p; rfl

private def zeroEquiv : ColorCompAllowed 1 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => rfl
    | cons p l =>
      have hp := h.1 p (by simp)
      have hs := h.2
      simp only [List.map_cons, List.sum_cons] at hs
      omega
  right_inv := by intro u; cases u; rfl

private def oneEquiv : ColorCompAllowed 1 1 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[(1, 1)], by simp⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      have hp := h.1 p (by simp)
      cases l with
      | nil =>
        obtain ⟨k, c⟩ := p
        have hs : k = 1 := h.2
        have hc : c = 1 := by omega
        subst k
        subst c
        rfl
      | cons q l =>
        have hq := h.1 q (by simp)
        have hs := h.2
        simp only [List.map_cons, List.sum_cons] at hs
        omega
  right_inv := by intro u; cases u; rfl

private theorem allowedFinite (n : ℕ) : Finite (ColorCompAllowed 1 n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact Finite.of_equiv Unit zeroEquiv.symm
  | one => exact Finite.of_equiv Unit oneEquiv.symm
  | more n ih₀ ih₁ =>
    have : Finite (ColorCompAllowed 1 n) := ih₀
    have : Finite (ColorCompAllowed 1 (n + 1)) := ih₁
    exact Finite.of_equiv _ (leadingEquiv n).symm

private theorem ccoAllowed_step (n : ℕ) :
    ccoAllowed 1 (n + 2) = ccoAllowed 1 (n + 1) + (ccoAllowed 1 (n + 1) + ccoAllowed 1 n) := by
  have := allowedFinite n
  have := allowedFinite (n + 1)
  unfold ccoAllowed
  simpa only [Nat.card_sum] using Nat.card_congr (leadingEquiv n)

private def evenSum (n r : ℕ) : ℕ := ∑ m ∈ Finset.range r, 2 ^ m * n.choose (2 * m)

private def oddSum (n r : ℕ) : ℕ := ∑ m ∈ Finset.range r, 2 ^ m * n.choose (2 * m + 1)

private theorem oddSum_step (n r : ℕ) : oddSum (n + 1) r = evenSum n r + oddSum n r := by
  unfold evenSum oddSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [Nat.choose_succ_succ', mul_add]

private theorem evenSum_step (n r : ℕ) :
    evenSum (n + 1) (r + 1) = evenSum n (r + 1) + 2 * oddSum n r := by
  unfold evenSum oddSum
  rw [Finset.sum_range_succ' (f := fun m => 2 ^ m * (n + 1).choose (2 * m)),
    Finset.sum_range_succ' (f := fun m => 2 ^ m * n.choose (2 * m))]
  simp only [mul_zero, Nat.choose_zero_right, pow_zero, one_mul]
  rw [add_right_comm _ 1, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Nat.choose_succ_succ', pow_succ]
  ring

private theorem evenSum_of_le_one (n r : ℕ) (hn : n ≤ 1) : evenSum n (r + 1) = 1 := by
  unfold evenSum
  rw [Finset.sum_range_succ']
  have hzero (m : ℕ) : n.choose (2 * (m + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [hzero]

-- Keeping the upper limit variable lets Pascal's identity use the same cutoff in both parities.
private theorem ccoAllowed_eq_evenSum (n r : ℕ) (hr : n / 2 < r) :
    ccoAllowed 1 n = evenSum n r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  induction n using Nat.twoStepInduction generalizing r with
  | zero =>
    rw [ccoAllowed, Nat.card_congr zeroEquiv, Nat.card_unique, evenSum_of_le_one 0 r (by decide)]
  | one =>
    rw [ccoAllowed, Nat.card_congr oneEquiv, Nat.card_unique, evenSum_of_le_one 1 r (by decide)]
  | more n ih₀ ih₁ =>
    -- At this cutoff the last summand for `n` is already zero.
    have hpad : evenSum n (r + 1) = evenSum n r := by
      unfold evenSum
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : n < 2 * r), mul_zero,
        add_zero]
    have hstep := evenSum_step n r
    rw [ccoAllowed_step, ih₁ r (by omega), ih₀ r (by omega), evenSum_step (n + 1), oddSum_step]
    change evenSum (n + 1) (r + 1) + (evenSum (n + 1) (r + 1) + evenSum n (r + 1)) =
      evenSum (n + 1) (r + 1) + 2 * (evenSum n r + oddSum n r)
    omega

/-- **Binomial sum for n-color compositions with colors 1 and 2.** For every natural number
$n \ge 1$, the number $\operatorname{cco}_{1,2}(n)$ of $n$-color compositions of $n$ in which
every part has color $1$ or $2$ satisfies
$$\operatorname{cco}_{1,2}(n) = \sum_{m=0}^{\lfloor n/2 \rfloor} 2^m \binom{n}{2m}.$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 3. -/
theorem ccoAllowed_one_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    ccoAllowed 1 n =
      ∑ m ∈ Finset.range (n / 2 + 1), 2 ^ m * Nat.choose n (2 * m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact ccoAllowed_eq_evenSum (k + 1) _ (Nat.lt_succ_self _)

-- At a fixed length, record each part's excess above its color and the upper-color positions.
private abbrev AllowedVectors (b n m : ℕ) :=
  {p : (Fin m → ℕ) × Finset (Fin m) // b * m + (∑ j, p.1 j) + p.2.card = n}

private def partAt (b : ℕ) {m : ℕ} (f : Fin m → ℕ) (s : Finset (Fin m))
    (j : Fin m) : ℕ × ℕ :=
  let c := b + if j ∈ s then 1 else 0
  (c + f j, c)

private theorem sum_partAt (b : ℕ) {m : ℕ} (f : Fin m → ℕ) (s : Finset (Fin m)) :
    ((List.ofFn (partAt b f s)).map Prod.fst).sum = b * m + (∑ j, f j) + s.card := by
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, partAt, Finset.sum_add_distrib]
  have hs : (∑ j : Fin m, if j ∈ s then (1 : ℕ) else 0) = s.card := by
    rw [← Finset.sum_filter]
    simp
  rw [hs]
  simp [Nat.mul_comm, add_right_comm]

private noncomputable def allowedLengthEquiv (b n m : ℕ) (hb : 1 ≤ b) :
    AllowedVectors b n m ≃ {p : ColorCompAllowed b n // p.val.length = m} := by
  let decode (p : AllowedVectors b n m) : {p : ColorCompAllowed b n // p.val.length = m} :=
    ⟨⟨List.ofFn (partAt b p.1.1 p.1.2), by
      refine ⟨List.forall_mem_ofFn_iff.mpr ?_, (sum_partAt b _ _).trans p.2⟩
      intro j
      by_cases hj : j ∈ p.1.2 <;> simp [partAt, hj, hb]⟩, List.length_ofFn⟩
  refine Equiv.ofBijective decode ⟨?_, ?_⟩
  · intro p q h
    have hparts (j : Fin m) : partAt b p.1.1 p.1.2 j = partAt b q.1.1 q.1.2 j :=
      congrFun (List.ofFn_injective (congrArg (fun r => r.val.val) h)) j
    have hs : p.1.2 = q.1.2 := by
      ext j
      have hc := congrArg Prod.snd (hparts j)
      by_cases hp : j ∈ p.1.2 <;> by_cases hq : j ∈ q.1.2 <;>
        simp [partAt, hp, hq] at hc ⊢
    apply Subtype.ext
    refine Prod.ext (funext fun j => ?_) hs
    have hf := congrArg Prod.fst (hparts j)
    simpa [partAt, hs] using hf
  · intro p
    let get (j : Fin m) := p.val.val[j.val]'(by simpa only [p.2] using j.isLt)
    let f (j : Fin m) := (get j).1 - (get j).2
    let s := Finset.univ.filter fun j : Fin m => (get j).2 = b + 1
    have hparts (j : Fin m) : partAt b f s j = get j := by
      have hj : get j ∈ p.val.val := List.getElem_mem _
      have h := p.val.property.1 _ hj
      have hc : b + (if j ∈ s then 1 else 0) = (get j).2 := by
        rcases h.2.2 with hc | hc <;> simp [s, hc]
      apply Prod.ext
      · simp [partAt, hc, f, Nat.add_sub_of_le h.2.1]
      · exact hc
    have hlist : List.ofFn (partAt b f s) = p.val.val := by
      rw [show partAt b f s = get from funext hparts]
      apply List.ext_getElem
      · simp [p.2]
      · intro j hj hj'
        rw [List.getElem_ofFn]
    refine ⟨⟨(f, s), ?_⟩, Subtype.ext (Subtype.ext hlist)⟩
    rw [← sum_partAt, hlist]
    exact p.val.property.2

private def allowedLength {b n : ℕ} (hn : 1 ≤ n) (p : ColorCompAllowed b n) :
    ↥(Finset.Icc 1 n) := by
  refine ⟨p.val.length, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · cases h : p.val with
    | nil =>
      have hs := p.property.2
      simp [h] at hs
      omega
    | cons => simp
  · have h := List.length_le_sum_of_one_le (p.val.map Prod.fst) (by
      intro k hk
      obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hk
      exact (p.property.1 pc hpc).1.trans (p.property.1 pc hpc).2.1)
    simpa only [List.length_map, p.property.2] using h

private abbrev Excesses (m i : ℕ) := {f : Fin m → ℕ // ∑ j, f j = i}

private abbrev UpperPositions (m k : ℕ) := {s : Finset (Fin m) // s.card = k}

-- For a feasible length, the sum of the excesses determines the number of upper colors.
private def allowedExcessEquiv {b n m : ℕ} (h : b * m ≤ n) :
    AllowedVectors b n m ≃
      Σ i : ↥(Finset.Icc 0 (n - b * m)), Excesses m i × UpperPositions m (n - b * m - i) where
  toFun p :=
    ⟨⟨∑ j, p.1.1 j, Finset.mem_Icc.mpr ⟨Nat.zero_le _, by have := p.2; omega⟩⟩,
      ⟨⟨p.1.1, rfl⟩, ⟨p.1.2, by
        change p.1.2.card = n - b * m - (∑ j, p.1.1 j)
        have := p.2
        omega⟩⟩⟩
  invFun p := ⟨(p.2.1.1, p.2.2.1), by
    have hi := (Finset.mem_Icc.mp p.1.2).2
    have hf := p.2.1.2
    have hs := p.2.2.2
    change b * m + (∑ j, p.2.1.1 j) + p.2.2.1.card = n
    omega⟩
  left_inv p := rfl
  right_inv := by
    rintro ⟨⟨i, hi⟩, ⟨f, hf⟩, ⟨s, hs⟩⟩
    change (∑ j, f j) = i at hf
    subst i
    rfl

@[instance_reducible]
private noncomputable def excessesFintype (m i : ℕ) : Fintype (Excesses m i) :=
  Fintype.ofEquiv _ (Sym.equivNatSumOfFintype (Fin m) i)

private theorem isEmpty_allowedVectors {b n m : ℕ} (h : ¬ b * m ≤ n) :
    IsEmpty (AllowedVectors b n m) :=
  ⟨fun p => h (by have := p.2; omega)⟩

private theorem finite_allowedVectors (b n m : ℕ) : Finite (AllowedVectors b n m) := by
  by_cases h : b * m ≤ n
  · let (i : ↥(Finset.Icc 0 (n - b * m))) := excessesFintype m i
    exact Finite.of_equiv _ (allowedExcessEquiv h).symm
  · let := isEmpty_allowedVectors h
    infer_instance

private theorem card_excesses (m i : ℕ) (hm : 1 ≤ m) :
    Nat.card (Excesses m i) = Nat.choose (i + m - 1) (m - 1) := by
  classical
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin m) i), Sym.natCard_sym_eq_choose,
    Nat.card_fin]
  rw [Nat.add_comm m i, ← Nat.choose_symm (by omega : i ≤ i + m - 1),
    show i + m - 1 - i = m - 1 by omega]

private theorem card_allowedVectors (b n m : ℕ) (hm : 1 ≤ m) :
    Nat.card (AllowedVectors b n m) =
      ∑ i ∈ Finset.Icc 0 (n - b * m),
        if b * m + i ≤ n then Nat.choose (i + m - 1) (m - 1) * Nat.choose m (n - b * m - i)
        else 0 := by
  by_cases h : b * m ≤ n
  · let (i : ↥(Finset.Icc 0 (n - b * m))) := excessesFintype m i
    rw [Nat.card_congr (allowedExcessEquiv h), Nat.card_sigma,
      ← Finset.sum_coe_sort (Finset.Icc 0 (n - b * m))]
    apply Finset.sum_congr rfl
    intro i _
    have hi := (Finset.mem_Icc.mp i.property).2
    rw [ite_eq_left (by omega), Nat.card_prod, card_excesses m i hm]
    simp [UpperPositions, Nat.card_eq_fintype_card, Fintype.card_finset_len]
  · rw [Nat.card_eq_zero.mpr (.inl (isEmpty_allowedVectors h))]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)).symm

/-- **Double-sum formula for n-color compositions with two consecutive colors.** Let $b \ge 1$
and $n \ge 1$ be natural numbers, and let $\operatorname{cco}_{b,b+1}(n)$ be the number of
$n$-color compositions of $n$ in which every part has color $b$ or $b+1$. Then
$$\operatorname{cco}_{b,b+1}(n) = \sum_{m=1}^{n} \sum_{i=0}^{n-bm}
\binom{i+m-1}{m-1} \binom{m}{n-bm-i},$$
where the upper limit $n - bm$ is read as $0$ when $bm > n$, and every term with $bm + i > n$
is $0$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 1. -/
theorem ccoAllowed_eq_sum (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    ccoAllowed b n =
      ∑ m ∈ Finset.Icc 1 n,
        ∑ i ∈ Finset.Icc 0 (n - b * m),
          if b * m + i ≤ n then
            Nat.choose (i + m - 1) (m - 1) *
              Nat.choose m (n - b * m - i)
          else 0 := by
  let e : ColorCompAllowed b n ≃ Σ m : ↥(Finset.Icc 1 n), AllowedVectors b n m :=
    (Equiv.sigmaFiberEquiv (allowedLength hn)).symm.trans <|
      Equiv.sigmaCongrRight fun m =>
        (Equiv.subtypeEquivRight fun _ => Subtype.ext_iff).trans (allowedLengthEquiv b n m hb).symm
  let (m : ↥(Finset.Icc 1 n)) := finite_allowedVectors b n m
  rw [ccoAllowed, Nat.card_congr e, Nat.card_sigma, ← Finset.sum_coe_sort (Finset.Icc 1 n)]
  exact Finset.sum_congr rfl fun m _ => card_allowedVectors b n m (Finset.mem_Icc.mp m.2).1

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
