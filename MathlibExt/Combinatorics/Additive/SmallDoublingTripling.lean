/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Sum

/-!
# Small doubling does not force small tripling in groups (AIM Problem 3.5)

Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.5 (T. Tao) and
Tao's comment. UnsolvedMath record UM-20001117 (`AIM-COMBINATORICS-0242`), dataset
ulamai/UnsolvedMath v1.8.0.

We use the subgroup-plus-one-point construction from Sections 1 and 3 of
[T. Tao, *Product set estimates for non-commutative groups*](https://arxiv.org/abs/math/0601431).
The subgroup translates only the first copy of `ZMod m`, and the extra
permutation swaps the copies. Hence the two translations in a product
`h(a) * x * h(b)` can be recovered independently.

The namespace is retained for compatibility with the original statement.
The follow-up questions from the AIM problem list are not treated here.
-/

namespace MathlibExt.Combinatorics.SmallDoublingTriplingAIMCombinatoricsProblem242Wanted

open scoped Pointwise

/-- **Tao's small-doubling question (AIM Problem 3.5).** The proposition that small doubling
forces small tripling uniformly in all groups: there is a function $f : \mathbb{R} \to \mathbb{R}$
such that for every group $G$, every finite nonempty subset $A \subseteq G$ and every real number
$K$, if $|A \cdot A| \le K |A|$ then $|A \cdot A \cdot A| \le f(K) |A|$. Here
$A \cdot A = \{ab : a, b \in A\}$ and $A \cdot A \cdot A = \{abc : a, b, c \in A\}$. -/
@[expose] public def smallDoublingImpliesSmallTripling : Prop :=
  ∃ f : ℝ → ℝ, ∀ (G : Type) [Group G] [DecidableEq G] (A : Finset G) (K : ℝ), A.Nonempty →
    ((A * A).card : ℝ) ≤ K * A.card → ((A * A * A).card : ℝ) ≤ f K * A.card

private abbrev SwapGroup (m : ℕ) := Equiv.Perm (ZMod m ⊕ ZMod m)

private def leftTranslation {m : ℕ} (a : ZMod m) : SwapGroup m :=
  Equiv.sumCongr (Equiv.addLeft a) (Equiv.refl _)

private def swap (m : ℕ) : SwapGroup m := Equiv.sumComm _ _

private theorem leftTranslation_mul {m : ℕ} (a b : ZMod m) :
    leftTranslation a * leftTranslation b = leftTranslation (a + b) := by
  ext (y | y) <;> simp [leftTranslation, add_assoc]

private theorem swap_mul_swap (m : ℕ) : swap m * swap m = 1 := by
  ext (y | y) <;> rfl

private def translations (m : ℕ) [NeZero m] : Finset (SwapGroup m) :=
  Finset.univ.map ⟨leftTranslation, fun a b h ↦ by
    have h' := DFunLike.congr_fun h (Sum.inl (0 : ZMod m))
    simpa [leftTranslation] using h'⟩

private theorem mem_translations {m : ℕ} [NeZero m] (a : ZMod m) :
    leftTranslation a ∈ translations m :=
  Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩

private def witness (m : ℕ) [NeZero m] : Finset (SwapGroup m) := insert (swap m) (translations m)

private theorem witness_bounds (m : ℕ) [NeZero m] :
    (witness m).Nonempty ∧ (witness m).card ≤ 2 * m ∧
    (witness m * witness m).card ≤ 3 * (witness m).card ∧
    m * m ≤ (witness m * witness m * witness m).card := by
  let H := translations m
  let x := swap m
  let A := witness m
  have hx : x ∈ A := Finset.mem_insert_self _ _
  have hHA : H ⊆ A := Finset.subset_insert _ _
  have hHcard : H.card = m := (Finset.card_map _).trans (ZMod.card m)
  have hAcard : A.card ≤ 2 * m := by
    have h := Finset.card_insert_le x H
    change A.card ≤ H.card + 1 at h
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    omega
  have hone : (1 : SwapGroup m) ∈ H := by
    have hzero : leftTranslation (0 : ZMod m) = 1 := by
      ext (y | y) <;> simp [leftTranslation, Equiv.Perm.one_apply]
    rw [← hzero]
    exact mem_translations 0
  have hHH : H * H ⊆ H := by
    apply Finset.mul_subset_iff.mpr
    intro a ha b hb
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', _, rfl⟩ := Finset.mem_map.mp hb
    change leftTranslation a' * leftTranslation b' ∈ H
    rw [leftTranslation_mul]
    exact mem_translations _
  -- In the square, the four choices of factors give only three sets.
  have hAA : A * A ⊆ H ∪ H * {x} ∪ {x} * H := by
    change insert x H * insert x H ⊆ _
    rw [← Finset.singleton_union, Finset.union_mul, Finset.mul_union, Finset.mul_union,
      Finset.singleton_mul_singleton, swap_mul_swap]
    have hH : H ⊆ H ∪ H * {x} ∪ {x} * H :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have hHx : H * {x} ⊆ H ∪ H * {x} ∪ {x} * H :=
      Finset.subset_union_right.trans Finset.subset_union_left
    exact Finset.union_subset
      (Finset.union_subset ((Finset.singleton_subset_iff.mpr hone).trans hH)
        Finset.subset_union_right)
      (Finset.union_subset hHx (hHH.trans hH))
  have hDouble : (A * A).card ≤ 3 * A.card := by
    calc
      (A * A).card ≤ (H ∪ H * {x} ∪ {x} * H).card := Finset.card_le_card hAA
      _ ≤ (H ∪ H * {x}).card + ({x} * H).card := Finset.card_union_le ..
      _ ≤ H.card + (H * {x}).card + ({x} * H).card :=
        Nat.add_le_add_right (Finset.card_union_le ..) _
      _ = 3 * H.card := by rw [Finset.card_mul_singleton, Finset.card_singleton_mul]; omega
      _ ≤ 3 * A.card := Nat.mul_le_mul_left _ (Finset.card_le_card hHA)
  -- The images of the two zeros recover the two translation parameters.
  let pairProduct (p : ZMod m × ZMod m) := leftTranslation p.1 * x * leftTranslation p.2
  have hpair : Function.Injective pairProduct := by
    intro a b hab
    have ha := DFunLike.congr_fun hab (Sum.inr (0 : ZMod m))
    have hb := DFunLike.congr_fun hab (Sum.inl (0 : ZMod m))
    exact Prod.ext (by simpa [pairProduct, x, swap, leftTranslation, Equiv.Perm.mul_apply] using ha)
      (by simpa [pairProduct, x, swap, leftTranslation, Equiv.Perm.mul_apply] using hb)
  have hTriple : m * m ≤ (A * A * A).card := by
    have h := Finset.card_le_card_of_injOn (s := Finset.univ) pairProduct (t := A * A * A)
      (fun p _ ↦ Finset.mul_mem_mul (Finset.mul_mem_mul (hHA (mem_translations p.1)) hx)
        (hHA (mem_translations p.2))) hpair.injOn
    simpa [Fintype.card_prod, ZMod.card] using h
  exact ⟨⟨x, hx⟩, hAcard, hDouble, hTriple⟩

/--
**Small doubling does not imply small tripling.** There is no function
$f : \mathbb{R} \to \mathbb{R}$ such that for every group $G$, every finite nonempty subset
$A \subseteq G$ and every real number $K$ with $|A \cdot A| \le K |A|$ one has
$|A \cdot A \cdot A| \le f(K) |A|$. Here $A \cdot A = \{ab : a, b \in A\}$ and
$A \cdot A \cdot A = \{abc : a, b, c \in A\}$.

B. Green and M.-C. Chang pointed out the counterexample $A = H \cup \{x\}$ with $H$ a finite
non-normal subgroup and $x$ outside the normalizer of $H$: then $|A \cdot A|$ is comparable to
$|A|$, while $|A \cdot A \cdot A|$ can be much larger.

Source: AIM workshop Recent trends in
additive combinatorics (2004), problem list collected by E. Croot and V. F. Lev,
https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.5 (T. Tao) and Tao's comment;
resolution: Tao's comment on Problem 3.5 in the AIM problem list (counterexample pointed out by B.
Green and M.-C. Chang); T. Tao, Product set estimates for non-commutative groups, Combinatorica 28
(2008), 547-594, arXiv:math/0601431, comment to Problem 3.5: 'the problem as stated is false, as it
follows by considering A = H ∪ {x} where H is a non-normal subgroup and x is not in the normalizer
of H'; Tao's paper, Section 1 ('if A is the union of a subgroup and a point, then A · A will be
small, but higher products such as A · A · A can be large') and Section 3 (A = H ∪ {x}, H a finite
subgroup, x outside its normalizer: A² has size comparable to A, but A³ can be much larger),
https://aimath.org/WWN/additivecomb/additivecomb.pdf.
-/
public theorem smallDoublingImpliesSmallTripling_refuted :
    ¬ smallDoublingImpliesSmallTripling := by
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * max (f 3) 0)
  let m := n + 1
  let A := witness m
  obtain ⟨hA, hcard, hDouble, hTriple⟩ := witness_bounds m
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.succ_pos n
  have hlarge : 2 * max (f 3) 0 < (m : ℝ) :=
    hn.trans_le (by exact_mod_cast Nat.le_succ n)
  have hupper := hf (SwapGroup m) A 3 hA (by exact_mod_cast hDouble)
  have hcard' : (A.card : ℝ) ≤ 2 * m := by exact_mod_cast hcard
  have hTriple' : (m : ℝ) * m ≤ (A * A * A).card := by exact_mod_cast hTriple
  have hlt : f 3 * A.card < (m : ℝ) * m := calc
    _ ≤ max (f 3) 0 * A.card := mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)
    _ ≤ max (f 3) 0 * (2 * m) := mul_le_mul_of_nonneg_left hcard' (le_max_right ..)
    _ = (2 * max (f 3) 0) * m := by rw [← mul_assoc, mul_comm (max (f 3) 0)]
    _ < (m : ℝ) * m := mul_lt_mul_of_pos_right hlarge hm
  exact (hlt.trans_le (hTriple'.trans hupper)).false

end MathlibExt.Combinatorics.SmallDoublingTriplingAIMCombinatoricsProblem242Wanted
