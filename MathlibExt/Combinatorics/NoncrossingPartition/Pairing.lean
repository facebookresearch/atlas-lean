/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Noncrossing pair partitions are counted by the Catalan numbers

A *pair partition* of `{0, …, n - 1}` is a set partition all of whose blocks have exactly two
elements. The noncrossing pair partitions of `{0, …, 2k - 1}` are counted by the Catalan number
`C_k`, and there are none on an odd number of points. This is the combinatorial core of the moment
method for Wigner's semicircle law and of the free central limit theorem: the `n`-th moment of the
semicircle law is the number of noncrossing pair partitions of `{1, …, n}`.

The count goes through noncrossing perfect matchings, encoded as functions `f : ℕ → ℕ` that are
fixed-point-free involutions of `{0, …, n - 1}` (and the identity elsewhere) and are *nested*: if
`a < b < f a` then `a < f b < f a`. Splitting off the partner `f 0 = j + 1` of the first point
leaves a noncrossing matching of the `j` points strictly inside the arc and one of the `n - j - 2`
points to its right, which gives the Catalan recursion
`M(n + 1) = ∑_{j < n} M(j) M(n - 1 - j)` (Anderson, Guionnet and Zeitouni, §2.1.1, the recursion
`γ_k = ∑ γ_{k-j} γ_{j-1}` for noncrossing partitions, here restricted to pairings).

## Main definitions

* `NoncrossingPartition.IsNCMatching n f`: `f` is a noncrossing perfect matching of
  `{0, …, n - 1}`.
* `NoncrossingPartition.IsPairPartition P`: every block of `P` has two elements.

## Main results

* `NoncrossingPartition.card_ncMatching_succ`: the recursion through the partner of the first point.
* `NoncrossingPartition.pairPartitionEquivNCMatching`: noncrossing pair partitions of `Fin n` are
  the noncrossing perfect matchings of `{0, …, n - 1}`.
* `NoncrossingPartition.card_noncrossing_pairPartition_two_mul`: there are `C_k` noncrossing pair
  partitions of `Fin (2k)`.
* `NoncrossingPartition.card_noncrossing_pairPartition_two_mul_add_one`: there are none of
  `Fin (2k + 1)`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
  pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1.1
  (Definition 2.1.4
  and the recursion for noncrossing partitions) and Proposition 2.1.11 (noncrossing pair partitions
  of `{1, …, k}` index the Wigner words, hence the semicircle moments).

-/

@[expose] public section

open Finset

namespace NoncrossingPartition

/-! ### Noncrossing perfect matchings -/

/-- **Noncrossing perfect matching.** `f` is a noncrossing perfect matching of `{0, …, n - 1}`:
a fixed-point-free involution of
`{0, …, n - 1}`, equal to the identity from `n` on, whose arcs `{a, f a}` are nested or disjoint
(if `a < b < f a` then `a < f b < f a`). -/
structure IsNCMatching (n : ℕ) (f : ℕ → ℕ) : Prop where
  lt : ∀ i < n, f i < n
  ne : ∀ i < n, f i ≠ i
  invol : ∀ i < n, f (f i) = i
  nested : ∀ a b, a < b → b < f a → a < f b ∧ f b < f a
  fix : ∀ i, n ≤ i → f i = i

/-- **The type of noncrossing perfect matchings** of `{0, …, n - 1}`. -/
def NCMatching (n : ℕ) := {f : ℕ → ℕ // IsNCMatching n f}

instance (n : ℕ) : Finite (NCMatching n) := by
  refine Finite.of_injective
    (fun f : NCMatching n => fun i : Fin n => (⟨f.1 i, f.2.lt i i.2⟩ : Fin n)) ?_
  intro f g h
  apply Subtype.ext
  funext i
  by_cases hi : i < n
  · have := congrFun h ⟨i, hi⟩
    simpa using congrArg Fin.val this
  · rw [f.2.fix i (by omega), g.2.fix i (by omega)]

/- The identity is the unique noncrossing perfect matching of the empty set. -/
theorem card_ncMatching_zero : Nat.card (NCMatching 0) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨id, ⟨by simp, by simp, by simp, fun a b h1 h2 => by simp at h2; omega, by simp⟩⟩,
    fun f => Subtype.ext ?_⟩
  funext i
  exact f.2.fix i (Nat.zero_le i)

section Split

variable {n j m : ℕ} {f : ℕ → ℕ}

/- Points strictly inside the arc from `0` to `f 0 = j + 1` are matched inside it. -/
theorem IsNCMatching.inside (hf : IsNCMatching n f) (h0 : f 0 = j + 1) {i : ℕ} (h1 : 1 ≤ i)
    (hi : i ≤ j) : 1 ≤ f i ∧ f i ≤ j := by
  have := hf.nested 0 i (by omega) (by omega)
  omega

/- Points to the right of the arc from `0` to `f 0 = j + 1` are matched to the right of it. -/
theorem IsNCMatching.outside (hf : IsNCMatching n f) (h0 : f 0 = j + 1) {i : ℕ} (h1 : j + 2 ≤ i)
    (hi : i < n) : j + 2 ≤ f i ∧ f i < n := by
  have hlt := hf.lt i hi
  refine ⟨?_, hlt⟩
  by_contra hcon
  have hn0 : 0 < n := by omega
  rcases Nat.lt_or_ge (f i) 1 with hfi | hfi
  · have : f i = 0 := by omega
    have h := hf.invol i hi
    rw [this, h0] at h
    omega
  · rcases Nat.lt_or_ge (f i) (j + 1) with hfj | hfj
    · have := hf.inside h0 hfi (by omega : f i ≤ j)
      rw [hf.invol i hi] at this
      omega
    · have hfe : f i = j + 1 := by omega
      have h := hf.invol i hi
      rw [hfe, ← h0, hf.invol 0 hn0] at h
      omega

/- The matching induced on the `j` points inside the first arc, shifted down by one. -/
def insideMatching (j : ℕ) (f : ℕ → ℕ) : ℕ → ℕ := fun i => if i < j then f (i + 1) - 1 else i

/- The matching induced on the `m` points to the right of the first arc, ending at `j + 1`,
shifted down by `j + 2`. -/
def outsideMatching (j m : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < m then f (i + (j + 2)) - (j + 2) else i

theorem isNCMatching_insideMatching (hf : IsNCMatching n f) (h0 : f 0 = j + 1) :
    IsNCMatching j (insideMatching j f) := by
  have hin := fun i (h1 : 1 ≤ i) (hi : i ≤ j) => hf.inside h0 h1 hi
  have hn : j + 1 < n := by have := hf.lt 0 (by have := hf.fix 0; omega); omega
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a b hab hb => ?_, fun i hi => ?_⟩
  · have := hin (i + 1) (by omega) (by omega)
    simp only [insideMatching, ite_eq_left hi]
    omega
  · have := hin (i + 1) (by omega) (by omega)
    have := hf.ne (i + 1) (by omega)
    simp only [insideMatching, ite_eq_left hi]
    omega
  · have h1 := hin (i + 1) (by omega) (by omega)
    have h2 := hf.invol (i + 1) (by omega)
    simp only [insideMatching, ite_eq_left hi, ite_eq_left (by omega : f (i + 1) - 1 < j)]
    rw [Nat.sub_add_cancel h1.1, h2]
    omega
  · by_cases ha : a < j
    · simp only [insideMatching, ite_eq_left ha] at hb ⊢
      have hbj : b < j := by have := hin (a + 1) (by omega) (by omega); omega
      simp only [ite_eq_left hbj]
      have := hf.nested (a + 1) (b + 1) (by omega) (by omega)
      have := hin (b + 1) (by omega) (by omega)
      omega
    · simp only [insideMatching, ite_eq_right ha] at hb
      omega
  · simp only [insideMatching, ite_eq_right (by omega : ¬ i < j)]

theorem isNCMatching_outsideMatching (hf : IsNCMatching n f) (h0 : f 0 = j + 1)
    (hn : n = j + m + 2) : IsNCMatching m (outsideMatching j m f) := by
  have hout := fun i (h1 : j + 2 ≤ i) (hi : i < n) => hf.outside h0 h1 hi
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a b hab hb => ?_, fun i hi => ?_⟩
  · have := hout (i + (j + 2)) (by omega) (by omega)
    simp only [outsideMatching, ite_eq_left hi]
    omega
  · have := hout (i + (j + 2)) (by omega) (by omega)
    have := hf.ne (i + (j + 2)) (by omega)
    simp only [outsideMatching, ite_eq_left hi]
    omega
  · have h1 := hout (i + (j + 2)) (by omega) (by omega)
    have h2 := hf.invol (i + (j + 2)) (by omega)
    simp only [outsideMatching, ite_eq_left hi,
      ite_eq_left (by omega : f (i + (j + 2)) - (j + 2) < m)]
    rw [Nat.sub_add_cancel h1.1, h2]
    omega
  · by_cases ha : a < m
    · simp only [outsideMatching, ite_eq_left ha] at hb ⊢
      have hbm : b < m := by have := hout (a + (j + 2)) (by omega) (by omega); omega
      simp only [ite_eq_left hbm]
      have := hf.nested (a + (j + 2)) (b + (j + 2)) (by omega) (by omega)
      have := hout (b + (j + 2)) (by omega) (by omega)
      omega
    · simp only [outsideMatching, ite_eq_right ha] at hb
      omega
  · simp only [outsideMatching, ite_eq_right (by omega : ¬ i < m)]

/- Glue a matching `g` of `j` points and a matching `h` of `m` points into a matching of
`j + m + 2` points: `0` is matched to `j + 1`, `g` acts on `1, …, j` and `h` on
`j + 2, …, j + m + 1`. -/
def glue (j m : ℕ) (g h : ℕ → ℕ) : ℕ → ℕ := fun i =>
  if i = 0 then j + 1
  else if i ≤ j then g (i - 1) + 1
  else if i = j + 1 then 0
  else if i < j + m + 2 then h (i - (j + 2)) + (j + 2)
  else i

section GlueValues

variable {g h : ℕ → ℕ} {i : ℕ}

theorem glue_zero : glue j m g h 0 = j + 1 := by simp [glue]

theorem glue_inside (h1 : 1 ≤ i) (hi : i ≤ j) : glue j m g h i = g (i - 1) + 1 := by
  unfold glue; split_ifs <;> first | rfl | omega

theorem glue_mid : glue j m g h (j + 1) = 0 := by
  unfold glue; split_ifs <;> first | rfl | omega

theorem glue_outside (h1 : j + 2 ≤ i) (hi : i < j + m + 2) :
    glue j m g h i = h (i - (j + 2)) + (j + 2) := by
  unfold glue; split_ifs <;> first | rfl | omega

theorem glue_large (hi : j + m + 2 ≤ i) : glue j m g h i = i := by
  unfold glue; split_ifs <;> first | rfl | omega

end GlueValues

theorem region (i j m : ℕ) :
    i = 0 ∨ (1 ≤ i ∧ i ≤ j) ∨ i = j + 1 ∨ (j + 2 ≤ i ∧ i < j + m + 2) ∨ j + m + 2 ≤ i := by
  omega

theorem isNCMatching_glue {g h : ℕ → ℕ} (hg : IsNCMatching j g) (hh : IsNCMatching m h)
    (hn : n = j + m + 2) : IsNCMatching n (glue j m g h) := by
  subst hn
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a b hab hb => ?_, fun i hi => ?_⟩
  · rcases region i j m with r | r | r | r | r
    · subst r; rw [glue_zero]; omega
    · rw [glue_inside r.1 r.2]; have := hg.lt (i - 1) (by omega); omega
    · subst r; rw [glue_mid]; omega
    · rw [glue_outside r.1 r.2]; have := hh.lt (i - (j + 2)) (by omega); omega
    · omega
  · rcases region i j m with r | r | r | r | r
    · subst r; rw [glue_zero]; omega
    · rw [glue_inside r.1 r.2]; have := hg.ne (i - 1) (by omega); omega
    · subst r; rw [glue_mid]; omega
    · rw [glue_outside r.1 r.2]; have := hh.ne (i - (j + 2)) (by omega); omega
    · omega
  · rcases region i j m with r | r | r | r | r
    · subst r; rw [glue_zero, glue_mid]
    · have hl := hg.lt (i - 1) (by omega)
      rw [glue_inside r.1 r.2, glue_inside (by omega) (by omega), Nat.add_sub_cancel,
        hg.invol (i - 1) (by omega)]
      omega
    · subst r; rw [glue_mid, glue_zero]
    · have hl := hh.lt (i - (j + 2)) (by omega)
      rw [glue_outside r.1 r.2, glue_outside (by omega) (by omega), Nat.add_sub_cancel,
        hh.invol (i - (j + 2)) (by omega)]
      omega
    · omega
  · rcases region a j m with r | r | r | r | r
    · subst r
      rw [glue_zero] at hb
      have hl := hg.lt (b - 1) (by omega)
      rw [glue_zero, glue_inside (by omega) (by omega)]
      omega
    · rw [glue_inside r.1 r.2] at hb ⊢
      have hl := hg.lt (a - 1) (by omega)
      have hl' := hg.lt (b - 1) (by omega)
      have := hg.nested (a - 1) (b - 1) (by omega) (by omega)
      rw [glue_inside (by omega) (by omega)]
      omega
    · subst r; rw [glue_mid] at hb; omega
    · rw [glue_outside r.1 r.2] at hb ⊢
      have hl := hh.lt (a - (j + 2)) (by omega)
      have hl' := hh.lt (b - (j + 2)) (by omega)
      have := hh.nested (a - (j + 2)) (b - (j + 2)) (by omega) (by omega)
      rw [glue_outside (by omega) (by omega)]
      omega
    · rw [glue_large r] at hb; omega
  · exact glue_large hi

/- The two matchings induced inside and to the right of the first arc. -/
def splitFun (hn : n = j + m + 2) (f : {f : NCMatching n // f.1 0 = j + 1}) :
    NCMatching j × NCMatching m :=
  (⟨insideMatching j f.1.1, isNCMatching_insideMatching f.1.2 f.2⟩,
    ⟨outsideMatching j m f.1.1, isNCMatching_outsideMatching f.1.2 f.2 hn⟩)

/- The matching glued from a matching inside the first arc and one to its right. -/
def glueFun (hn : n = j + m + 2) (p : NCMatching j × NCMatching m) :
    {f : NCMatching n // f.1 0 = j + 1} :=
  ⟨⟨glue j m p.1.1 p.2.1, isNCMatching_glue p.1.2 p.2.2 hn⟩,
    glue_zero (m := m) (g := p.1.1) (h := p.2.1)⟩

/-- **Splitting off the first arc.** The noncrossing perfect matchings of `{0, …, n - 1}` in which
`0` is matched to `j + 1`, where `n = j + m + 2`, correspond to pairs of noncrossing perfect
matchings of the `j` points inside the arc and of the `m` points to its right. -/
def splitEquiv (hn : n = j + m + 2) :
    {f : NCMatching n // f.1 0 = j + 1} ≃ NCMatching j × NCMatching m where
  toFun := splitFun hn
  invFun := glueFun hn
  left_inv := by
    rintro ⟨⟨f, hf⟩, h0⟩
    change f 0 = j + 1 at h0
    apply Subtype.ext; apply Subtype.ext
    funext i
    simp only [splitFun, glueFun]
    rcases region i j m with r | r | r | r | r
    · subst r; rw [glue_zero, h0]
    · have := hf.inside h0 r.1 r.2
      rw [glue_inside r.1 r.2]
      simp only [insideMatching, ite_eq_left (by omega : i - 1 < j), Nat.sub_add_cancel r.1]
      omega
    · subst r
      rw [glue_mid, ← h0, hf.invol 0 (by have := hf.lt 0; have := hf.fix 0; omega)]
    · have := hf.outside h0 r.1 (by omega)
      rw [glue_outside r.1 r.2]
      simp only [outsideMatching, ite_eq_left (by omega : i - (j + 2) < m),
        Nat.sub_add_cancel r.1]
      omega
    · rw [glue_large r, hf.fix i (by omega)]
  right_inv := by
    rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> funext i
    · simp only [splitFun, glueFun]
      by_cases hi : i < j
      · simp only [insideMatching, ite_eq_left hi]
        rw [glue_inside (i := i + 1) (by omega) (by omega)]
        simp
      · simp only [insideMatching, ite_eq_right hi, hg.fix i (by omega)]
    · simp only [splitFun, glueFun]
      by_cases hi : i < m
      · simp only [outsideMatching, ite_eq_left hi]
        rw [glue_outside (i := i + (j + 2)) (by omega) (by omega)]
        simp
      · simp only [outsideMatching, ite_eq_right hi, hh.fix i (by omega)]

end Split

/- The partner of the first point, `f 0 - 1`, as an element of `Fin n`. -/
def firstPartner (n : ℕ) (f : NCMatching (n + 1)) : Fin n :=
  ⟨f.1 0 - 1, by have := f.2.lt 0 (by omega); have := f.2.ne 0 (by omega); omega⟩

/-- **Catalan recursion for noncrossing matchings**: splitting at the partner `j + 1` of the first
point, `M(n + 1) = ∑_{j < n} M(j) M(n - 1 - j)` (Anderson, Guionnet and Zeitouni, *An
Introduction to Random Matrices*, §2.1.1, the recursion for `γ_k` restricted to pairings). -/
theorem card_ncMatching_succ (n : ℕ) :
    Nat.card (NCMatching (n + 1)) =
      ∑ j ∈ range n, Nat.card (NCMatching j) * Nat.card (NCMatching (n - 1 - j)) := by
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv (firstPartner n)).symm, Nat.card_sigma,
    ← Fin.sum_univ_eq_sum_range (fun j => Nat.card (NCMatching j) *
      Nat.card (NCMatching (n - 1 - j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun f => ?_).trans
    (splitEquiv (j := j) (m := n - 1 - j) (by omega)))
  have h1 := f.2.lt 0 (by omega)
  have h2 := f.2.ne 0 (by omega)
  simp only [firstPartner, Fin.ext_iff]
  omega

/- Sum over `j < 2k + 1` split by parity. -/
private theorem sum_range_two_mul_add_one (F : ℕ → ℕ) (k : ℕ) :
    ∑ j ∈ range (2 * k + 1), F j =
      ∑ a ∈ range (k + 1), F (2 * a) + ∑ a ∈ range k, F (2 * a + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun a => F (2 * a)) (k + 1), sum_range_succ (fun a => F (2 * a + 1)) k,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    ring

/-- **Counting noncrossing perfect matchings.** The number of noncrossing perfect matchings of
`{0, …, n - 1}` is `C_{n/2}` for `n` even and `0` for `n` odd. -/
theorem card_ncMatching (n : ℕ) :
    Nat.card (NCMatching n) = if n % 2 = 0 then catalan (n / 2) else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | N
    · simp [card_ncMatching_zero]
    rw [card_ncMatching_succ]
    have hsum : ∑ j ∈ range N, Nat.card (NCMatching j) * Nat.card (NCMatching (N - 1 - j)) =
        ∑ j ∈ range N, (if j % 2 = 0 then catalan (j / 2) else 0) *
          (if (N - 1 - j) % 2 = 0 then catalan ((N - 1 - j) / 2) else 0) := by
      refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      rw [ih j (by omega), ih (N - 1 - j) (by omega)]
    rw [hsum]
    rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
    · rw [ite_eq_right (by omega)]
      refine sum_eq_zero fun j hj => ?_
      rw [mem_range] at hj
      by_cases hj2 : j % 2 = 0
      · rw [ite_eq_right (by omega : ¬ (2 * k - 1 - j) % 2 = 0), mul_zero]
      · rw [ite_eq_right hj2, zero_mul]
    · rw [ite_eq_left (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega, catalan_succ,
        Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (k - i)) (k + 1),
        sum_range_two_mul_add_one]
      have hodd : ∑ a ∈ range k, (if (2 * a + 1) % 2 = 0 then catalan ((2 * a + 1) / 2) else 0) *
          (if (2 * k + 1 - 1 - (2 * a + 1)) % 2 = 0 then
            catalan ((2 * k + 1 - 1 - (2 * a + 1)) / 2) else 0) = 0 :=
        sum_eq_zero fun a _ => by rw [ite_eq_right (by omega), zero_mul]
      rw [hodd, add_zero]
      refine sum_congr rfl fun a ha => ?_
      rw [mem_range] at ha
      rw [ite_eq_left (by omega), ite_eq_left (by omega), show 2 * a / 2 = a by omega,
        show (2 * k + 1 - 1 - 2 * a) / 2 = k - a by omega]

/-! ### Pair partitions -/

/-- **Pair partition.** A set partition is a pair partition if every block has exactly two
elements. -/
def IsPairPartition {n : ℕ} (P : SetPartition n) : Prop := ∀ b ∈ P.parts, b.card = 2

instance {n : ℕ} (P : SetPartition n) : Decidable (IsPairPartition P) := by
  unfold IsPairPartition; infer_instance

section Bridge

variable {n : ℕ}

/- In a pair partition, the block of `i` is `{i, j}` for some `j ≠ i`. -/
theorem IsPairPartition.exists_part_eq {P : SetPartition n} (hP : IsPairPartition P) (i : Fin n) :
    ∃ j, j ≠ i ∧ P.part i = {i, j} := by
  obtain ⟨x, y, hxy, hb⟩ := card_eq_two.1 (hP _ (part_mem_parts P i))
  have hi : i ∈ P.part i := mem_part_self P i
  rw [hb, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨y, hxy.symm, hb⟩
  · exact ⟨x, hxy, by rw [hb, pair_comm]⟩

/-- **Partner map of a pair partition.** The partner of `i` in a pair partition is
`(∑_{x ∈ block of i} x) - i`; the map is extended by the identity from `n` on. -/
def pairPartner (P : SetPartition n) (i : ℕ) : ℕ :=
  if h : i < n then (∑ x ∈ P.part ⟨i, h⟩, (x : ℕ)) - i else i

theorem pairPartner_spec {P : SetPartition n} (hP : IsPairPartition P) {i : ℕ} (hi : i < n) :
    ∃ hj : pairPartner P i < n, pairPartner P i ≠ i ∧
      P.part ⟨i, hi⟩ = {⟨i, hi⟩, ⟨pairPartner P i, hj⟩} := by
  obtain ⟨j, hji, hb⟩ := hP.exists_part_eq ⟨i, hi⟩
  have hval : pairPartner P i = j := by
    have hne : (⟨i, hi⟩ : Fin n) ∉ ({j} : Finset (Fin n)) := by
      simpa [eq_comm] using hji
    simp only [pairPartner, dite_eq_left hi, hb, sum_insert hne, sum_singleton]
    omega
  refine ⟨hval ▸ j.2, ?_, ?_⟩
  · rw [hval]; exact fun h => hji (Fin.ext h)
  · rw [hb]; congr 2; exact Fin.ext hval.symm

theorem isNCMatching_pairPartner {P : SetPartition n} (hP : IsPairPartition P)
    (hnc : IsNoncrossing P) : IsNCMatching n (pairPartner P) := by
  have hspec := fun i (hi : i < n) => pairPartner_spec hP hi
  have hpart : ∀ i (hi : i < n) (k : Fin n),
      k ∈ P.part ⟨i, hi⟩ ↔ (k : ℕ) = i ∨ (k : ℕ) = pairPartner P i := by
    intro i hi k
    obtain ⟨hj, -, hb⟩ := hspec i hi
    rw [hb, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff]
  have hinv : ∀ i (hi : i < n), pairPartner P (pairPartner P i) = i := by
    intro i hi
    obtain ⟨hj, hne, hb⟩ := hspec i hi
    obtain ⟨hj', hne', hb'⟩ := hspec _ hj
    have hmem : (⟨pairPartner P i, hj⟩ : Fin n) ∈ P.part ⟨i, hi⟩ := by rw [hb]; simp
    have hsame := P.part_eq_of_mem (part_mem_parts P _) hmem
    have h2 : (⟨i, hi⟩ : Fin n) ∈ P.part ⟨pairPartner P i, hj⟩ := by
      rw [hsame]; exact mem_part_self P _
    rcases (hpart _ hj _).1 h2 with h | h
    · exact absurd h.symm hne
    · exact h.symm
  have hsame : ∀ i (hi : i < n) (k : Fin n), (k : ℕ) = pairPartner P i →
      P.part k = P.part ⟨i, hi⟩ := by
    intro i hi k hk
    exact P.part_eq_of_mem (part_mem_parts P _) ((hpart i hi k).2 (Or.inr hk))
  refine ⟨fun i hi => (hspec i hi).1, fun i hi => (hspec i hi).2.1, hinv, ?_, fun i hi => ?_⟩
  · intro a b hab hb
    have ha : a < n := by
      by_contra h; simp only [pairPartner, dite_eq_right h] at hb; omega
    have hfa := (hspec a ha).1
    have hbn : b < n := by omega
    have hfb := (hspec b hbn).1
    have hneb := (hspec b hbn).2.1
    have hfbfa : pairPartner P b ≠ pairPartner P a := by
      intro h; have := congrArg (pairPartner P) h; rw [hinv b hbn, hinv a ha] at this; omega
    have hfba : pairPartner P b ≠ a := by
      intro h; have := congrArg (pairPartner P) h; rw [hinv b hbn] at this; omega
    by_contra hcon
    apply hnc
    have hdiff : ∀ (x y : Fin n), (y : ℕ) ≠ x → (y : ℕ) ≠ pairPartner P x →
        P.part x ≠ P.part y := by
      intro x y h1 h2 h
      have : y ∈ P.part x := by rw [h]; exact mem_part_self P y
      rcases (hpart x x.2 y).1 this with h3 | h3 <;> contradiction
    rcases Nat.lt_or_gt_of_ne hfbfa with hlt | hgt
    · -- `f b < a`: the arcs `{f b, b}` and `{a, f a}` cross as `f b < a < b < f a`.
      have hlt' : pairPartner P b < a := by omega
      refine ⟨⟨pairPartner P b, hfb⟩, ⟨a, ha⟩, ⟨b, hbn⟩, ⟨pairPartner P a, hfa⟩,
        hlt', hab, hb, ?_, ?_, ?_⟩
      · rw [hsame b hbn ⟨pairPartner P b, hfb⟩ rfl]
      · exact (hsame a ha ⟨pairPartner P a, hfa⟩ rfl).symm
      · exact hdiff ⟨pairPartner P b, hfb⟩ ⟨a, ha⟩ (by simp; omega)
          (by simp only; rw [hinv b hbn]; omega)
    · -- `f a < f b`: the arcs cross as `a < b < f a < f b`.
      refine ⟨⟨a, ha⟩, ⟨b, hbn⟩, ⟨pairPartner P a, hfa⟩, ⟨pairPartner P b, hfb⟩,
        hab, hb, hgt, ?_, ?_, ?_⟩
      · exact (hsame a ha ⟨pairPartner P a, hfa⟩ rfl).symm
      · exact (hsame b hbn ⟨pairPartner P b, hfb⟩ rfl).symm
      · exact hdiff ⟨a, ha⟩ ⟨b, hbn⟩ (by simp; omega) (by simp only; omega)
  · simp [pairPartner, dite_eq_right (by omega : ¬ i < n)]

/- The setoid on `Fin n` whose classes are the arcs `{i, f i}` of a matching. -/
def matchingSetoid {f : ℕ → ℕ} (hf : IsNCMatching n f) : Setoid (Fin n) where
  r x y := (y : ℕ) = x ∨ (y : ℕ) = f x
  iseqv := by
    refine ⟨fun x => Or.inl rfl, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
    · rcases h with h | h
      · exact Or.inl h.symm
      · right; rw [h, hf.invol x x.2]
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · left; omega
      · right; rw [h2, h1]
      · right; omega
      · left; rw [h2, h1, hf.invol x x.2]

instance {f : ℕ → ℕ} (hf : IsNCMatching n f) : DecidableRel (matchingSetoid hf).r :=
  fun x y => by unfold matchingSetoid; dsimp only; infer_instance

/-- **The pair partition of a matching**, whose blocks are the arcs `{i, f i}` of a noncrossing
perfect matching `f`. -/
def matchingPartition {f : ℕ → ℕ} (hf : IsNCMatching n f) : SetPartition n :=
  Finpartition.ofSetoid (matchingSetoid hf)

theorem mem_part_matchingPartition {f : ℕ → ℕ} (hf : IsNCMatching n f) (x y : Fin n) :
    y ∈ (matchingPartition hf).part x ↔ (y : ℕ) = x ∨ (y : ℕ) = f x :=
  Finpartition.mem_part_ofSetoid_iff_rel

theorem part_matchingPartition {f : ℕ → ℕ} (hf : IsNCMatching n f) (x : Fin n) :
    (matchingPartition hf).part x = {x, ⟨f x, hf.lt x x.2⟩} := by
  ext y
  rw [mem_part_matchingPartition, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff]

theorem isPairPartition_matchingPartition {f : ℕ → ℕ} (hf : IsNCMatching n f) :
    IsPairPartition (matchingPartition hf) := by
  intro b hb
  obtain ⟨x, hx⟩ := (matchingPartition hf).nonempty_of_mem_parts hb
  rw [← (matchingPartition hf).part_eq_of_mem hb hx, part_matchingPartition]
  refine card_pair fun h => hf.ne x x.2 ?_
  exact (congrArg Fin.val h).symm

theorem isNoncrossing_matchingPartition {f : ℕ → ℕ} (hf : IsNCMatching n f) :
    IsNoncrossing (matchingPartition hf) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  have hc : (c : ℕ) = f a := by
    have : c ∈ (matchingPartition hf).part a := by rw [hac]; exact mem_part_self _ c
    rcases (mem_part_matchingPartition hf a c).1 this with h | h
    · exact absurd (Fin.ext h) (ne_of_gt (hab.trans hbc))
    · exact h
  have hd : (d : ℕ) = f b := by
    have : d ∈ (matchingPartition hf).part b := by rw [hbd]; exact mem_part_self _ d
    rcases (mem_part_matchingPartition hf b d).1 this with h | h
    · exact absurd (Fin.ext h) (ne_of_gt (hbc.trans hcd))
    · exact h
  have hab' : (a : ℕ) < b := hab
  have hbc' : (b : ℕ) < c := hbc
  have hcd' : (c : ℕ) < d := hcd
  have := hf.nested a b hab' (by omega)
  omega

/-- **Noncrossing pair partitions are noncrossing perfect matchings.** -/
def pairPartitionEquivNCMatching :
    {P : _root_.NoncrossingPartition n // IsPairPartition P.val} ≃ NCMatching n where
  toFun P := ⟨pairPartner P.1.val, isNCMatching_pairPartner P.2 P.1.2⟩
  invFun f := ⟨⟨matchingPartition f.2, isNoncrossing_matchingPartition f.2⟩,
    isPairPartition_matchingPartition f.2⟩
  left_inv := by
    rintro ⟨⟨P, hnc⟩, hP⟩
    have hf := isNCMatching_pairPartner hP hnc
    have hpart : ∀ x : Fin n, (matchingPartition hf).part x = P.part x := by
      intro x
      obtain ⟨hj, -, hb⟩ := pairPartner_spec hP x.2
      rw [part_matchingPartition, hb]
    apply Subtype.ext; apply Subtype.ext
    apply Finpartition.ext
    ext t
    constructor
    · intro ht
      obtain ⟨x, hx⟩ := (matchingPartition hf).nonempty_of_mem_parts ht
      rw [← (matchingPartition hf).part_eq_of_mem ht hx, hpart]
      exact part_mem_parts P x
    · intro ht
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
      rw [← P.part_eq_of_mem ht hx, ← hpart]
      exact part_mem_parts _ x
  right_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext i
    dsimp only
    by_cases hi : i < n
    · obtain ⟨hj, hne, hb⟩ := pairPartner_spec (isPairPartition_matchingPartition hf) hi
      rw [part_matchingPartition] at hb
      have hmem : (⟨pairPartner (matchingPartition hf) i, hj⟩ : Fin n) ∈
          ({⟨i, hi⟩, ⟨f i, hf.lt i hi⟩} : Finset (Fin n)) := by rw [hb]; simp
      rw [mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff] at hmem
      rcases hmem with h | h
      · exact absurd h hne
      · exact h
    · simp [pairPartner, dite_eq_right hi, hf.fix i (by omega)]

end Bridge

/-- **Noncrossing pair partitions of `{1, …, 2k}` are counted by the Catalan number `C_k`**
(Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices* (manuscript numbering),
§2.1.1 and
Proposition 2.1.11). -/
theorem card_noncrossing_pairPartition_two_mul (k : ℕ) :
    Fintype.card {P : _root_.NoncrossingPartition (2 * k) // IsPairPartition P.val} =
      catalan k := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr pairPartitionEquivNCMatching, card_ncMatching,
    ite_eq_left (by omega), show 2 * k / 2 = k by omega]

/-- **There is no pair partition of an odd number of points**, so no noncrossing one. -/
theorem card_noncrossing_pairPartition_two_mul_add_one (k : ℕ) :
    Fintype.card {P : _root_.NoncrossingPartition (2 * k + 1) // IsPairPartition P.val} = 0 := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr pairPartitionEquivNCMatching, card_ncMatching,
    ite_eq_right (by omega)]

/-- **Counting noncrossing pair partitions.** The number of noncrossing pair partitions of
`{1, …, n}` is `C_{n/2}` for `n` even and `0` for `n` odd (Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (manuscript numbering), §2.1.1 and Proposition 2.1.11). -/
theorem card_noncrossing_pairPartition (n : ℕ) :
    Fintype.card {P : _root_.NoncrossingPartition n // IsPairPartition P.val} =
      if n % 2 = 0 then catalan (n / 2) else 0 := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr pairPartitionEquivNCMatching, card_ncMatching]

end NoncrossingPartition
