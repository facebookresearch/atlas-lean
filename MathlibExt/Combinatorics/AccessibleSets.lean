/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Accessible sets and diffsequences

A set of positive gaps is accessible if every finite coloring of the positive integers admits
arbitrarily long monochromatic sequences with consecutive differences in that set.

For a union of two sets, we use the longest-sequence coloring described by Oscar Quester in
*On Some Properties of Accessible Sets*. If a coloring bounds the lengths of monochromatic
diffsequences for one part, refining each point's color by the longest length starting there
separates the ends of every gap in that part.

If the fractional part of every dilated gap lies in $[\varepsilon, 1 - 1/r]$ with $\varepsilon > 0$,
coloring by $r$ equal subintervals of $[0,1)$ bounds the length of a monochromatic diffsequence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Monochromatic sequences of positive integers.** Let $r$ and $k$ be natural numbers and let
$c$ color the positive integers with the colors $0, 1, \dots, r - 1$. A sequence
$x_0, \dots, x_{k-1}$ of positive integers is monochromatic for $c$ when $c(x_i) = c(x_j)$ for
all $i, j < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsMonochromatic {r k : ℕ} (c : ℕ+ → Fin r)
    (x : Fin k → ℕ+) : Prop :=
  ∀ i j, c (x i) = c (x j)

/-- **Arithmetic progressions with gap in $D$.** Let $D$ be a set of natural numbers and $k$ a
natural number. A sequence $x_0, \dots, x_{k-1}$ of positive integers is a $k$-term arithmetic
progression with gap in $D$ if there are a positive integer $a$ and an element $d \in D$ such
that $x_i = a + i d$ for every $i < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsDAP (D : Set ℕ) (k : ℕ) (x : Fin k → ℕ+) : Prop :=
  ∃ a : ℕ+, ∃ d ∈ D, ∀ i, (x i : ℕ) = a + (i : ℕ) * d

/-- **Characterization of arithmetic progressions with gap in $D$.** Let $D$ be a set of natural
numbers, $k$ a natural number and $x_0, \dots, x_{k-1}$ positive integers. Then
$x_0, \dots, x_{k-1}$ is a $k$-term arithmetic progression with gap in $D$ if and only if there
are a positive integer $a$ and an element $d \in D$ such that $x_i = a + i d$ for every $i < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isDAP_iff (D : Set ℕ) (k : ℕ) (x : Fin k → ℕ+) :
    IsDAP D k x ↔ ∃ a : ℕ+, ∃ d ∈ D, ∀ i, (x i : ℕ) = a + (i : ℕ) * d :=
  Iff.rfl

/-- **$r$-large sets.** Let $r$ be a natural number. A set $D$ of natural numbers is $r$-large when
every element of $D$ is positive, $r \ge 1$, and for every coloring $c$ of the positive integers
with the colors $0, 1, \dots, r - 1$ and every natural number $k \ge 1$ there are positive integers
$x_0, \dots, x_{k-1}$ that are monochromatic for $c$ and form a $D$-AP: there are a positive
integer $a$ and some $d \in D$ with $x_i = a + i d$ for all $i < k$.

Quantifying over every length $k \ge 1$ formalizes "arbitrarily long" monochromatic $D$-APs.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsRLarge (r : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
    ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
      ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧ IsDAP D k x

/-- **Characterization of $r$-large sets.** Let $r$ be a natural number and $D$ a set of natural
numbers. Then $D$ is $r$-large if and only if every element of $D$ is positive, $r \ge 1$, and for
every coloring $c$ of the positive integers with the colors $0, 1, \dots, r - 1$ and every natural
number $k \ge 1$ there are positive integers $x_0, \dots, x_{k-1}$ that are monochromatic for $c$
and form a $D$-AP: there are a positive integer $a$ and some $d \in D$ with $x_i = a + i d$ for
all $i < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isRLarge_iff (r : ℕ) (D : Set ℕ) :
    IsRLarge r D ↔ D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
      ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
        ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧ IsDAP D k x :=
  Iff.rfl

/-- **Large set.** A set $D$ of natural numbers is large when it is $r$-large for every natural
number $r \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsLarge (D : Set ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → IsRLarge r D

/-- **Characterization of large sets.** A set $D$ of natural numbers is large if and only if it
is $r$-large for every natural number $r \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isLarge_iff (D : Set ℕ) : IsLarge D ↔ ∀ r : ℕ, 1 ≤ r → IsRLarge r D :=
  Iff.rfl

/-- **Largeness is partition regular.** If $D_1, D_2 \subseteq \mathbb{N}$ and their union
$D = D_1 \cup D_2$ is large, then $D_1$ is large or $D_2$ is large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 4. -/
public theorem large_union_partition (D D₁ D₂ : Set ℕ)
    (hD : D = D₁ ∪ D₂) (hlarge : IsLarge D) :
    IsLarge D₁ ∨ IsLarge D₂ := by
  subst D
  have hpos := (hlarge 1 le_rfl).1
  refine or_iff_not_imp_left.mpr fun h₁ r₂ hr₂ =>
    ⟨Set.Subset.trans Set.subset_union_right hpos, hr₂, ?_⟩
  obtain ⟨r₁, hr₁, c₁, k₁, _, hbad⟩ :
      ∃ r, 1 ≤ r ∧ ∃ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k ∧
        ¬ ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧ IsDAP D₁ k x := by
    by_contra! hall
    exact h₁ fun r hr => ⟨Set.Subset.trans Set.subset_union_left hpos, hr, hall r hr⟩
  intro c₂ k₂ hk₂
  -- A single progression for the product coloring has both required lengths as prefixes.
  obtain ⟨x, hx, a, d, hd, hgap⟩ := (hlarge (r₁ * r₂) (Nat.mul_pos hr₁ hr₂)).2.2
    (fun n => finProdFinEquiv (c₁ n, c₂ n)) (max k₁ k₂) (hk₂.trans (le_max_right ..))
  have hpair (i j : Fin (max k₁ k₂)) := Prod.mk.inj (finProdFinEquiv.injective (hx i j))
  rcases hd with hd | hd
  · let ι := Fin.castLE (le_max_left k₁ k₂)
    exact (hbad ⟨x ∘ ι, fun i j => (hpair (ι i) (ι j)).1, a, d, hd, fun i => hgap (ι i)⟩).elim
  · let ι := Fin.castLE (le_max_right k₁ k₂)
    exact ⟨x ∘ ι, fun i j => (hpair (ι i) (ι j)).2, a, d, hd, fun i => hgap (ι i)⟩

/-- **$D$-diffsequences.** Let $D$ be a set of natural numbers and $k$ a natural number. A
finite sequence $x_0, \dots, x_{k-1}$ of integers is a $D$-diffsequence when for every $i$ with
$i + 1 < k$ there is $d \in D$ with $x_{i+1} - x_i = d$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (D-diffsequence). -/
public def IsDDiffSequence (D : Set ℕ) {k : ℕ} (x : Fin k → ℤ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < k),
    ∃ d ∈ D, x ⟨i + 1, h⟩ - x ⟨i, by omega⟩ = (d : ℤ)

/-- **Characterization of $D$-diffsequences.** Let $D$ be a set of natural numbers and
$x_0, \dots, x_{k-1}$ integers. Then $x_0, \dots, x_{k-1}$ is a $D$-diffsequence if and only if
for every $i$ with $i + 1 < k$ there is $d \in D$ such that $x_{i+1} - x_i = d$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (D-diffsequence). -/
public theorem isDDiffSequence_iff (D : Set ℕ) {k : ℕ} (x : Fin k → ℤ) :
    IsDDiffSequence D x ↔ ∀ (i : ℕ) (h : i + 1 < k),
      ∃ d ∈ D, x ⟨i + 1, h⟩ - x ⟨i, by omega⟩ = (d : ℤ) :=
  Iff.rfl

set_option linter.unusedVariables false in
/-- **Colorings avoiding long diffsequences under fractional-part bounds.** Let $r \ge 1$, let
$d_0 < d_1 < \cdots$ be a strictly increasing sequence of natural numbers with $d_0 > 0$, and let
$D = \{d_n : n \ge 0\}$. Suppose there are real numbers $\alpha$ and $\varepsilon > 0$ such that
for every $n$ the fractional part of $\alpha d_n$ lies in the closed interval
$[\varepsilon, (r-1)/r]$. Then there is a coloring of the positive integers with $r$ colors that
has no monochromatic $D$-diffsequence of positive integers of length
$\lceil 1/(r\varepsilon) \rceil + 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 12. -/
public theorem coloring_avoids_diffsequence_of_fractional_bounds
    (r : ℕ) (hr : 1 ≤ r) (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (α ε : ℝ) (hε : 0 < ε)
    (hfrac : ∀ n : ℕ, Int.fract (α * (d n : ℝ)) ∈
      Set.Icc ε (((r - 1 : ℕ) : ℝ) / (r : ℝ))) :
    ∃ c : ℕ+ → Fin r,
      ¬ ∃ x : Fin (Nat.ceil (((r : ℝ) * ε)⁻¹) + 1) → ℕ+,
        IsMonochromatic c x ∧
          IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ)) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r from hr)
  let phase (a : ℕ+) := Int.fract (α * (a : ℕ))
  let c (a : ℕ+) : Fin r := ⟨⌊r * phase a⌋₊, by
    apply (Nat.floor_lt' (Nat.ne_of_gt hr)).2
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (α * (a : ℕ))) hr'⟩
  refine ⟨c, ?_⟩
  rintro ⟨x, hx, hdiff⟩
  let k := Nat.ceil (((r : ℝ) * ε)⁻¹)
  -- Two phases in the same half-open color interval differ by less than its width.
  have near (i j : Fin (k + 1)) : phase (x i) - phase (x j) < 1 / r := by
    have heq := congrArg Fin.val (hx i j)
    have hu : r * phase (x i) < ((c (x i)).val : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [heq] at hu
    have hl : ((c (x j)).val : ℝ) ≤ r * phase (x j) :=
      Nat.floor_le (mul_nonneg hr'.le (Int.fract_nonneg _))
    apply (lt_div_iff₀ hr').2
    linarith only [hu, hl]
  subst D
  have step (i : Fin k) : phase (x i.castSucc) + ε ≤ phase (x i.succ) := by
    obtain ⟨_, ⟨n, rfl⟩, hgap⟩ := hdiff i i.succ.isLt
    have hsum : ((x i.succ : ℕ) : ℝ) = (x i.castSucc : ℕ) + (d n : ℝ) := by
      change ((x i.succ : ℕ) : ℤ) - (x i.castSucc : ℕ) = d n at hgap
      exact_mod_cast (sub_eq_iff_eq_add'.mp hgap)
    have hadd := Int.fract_add_eq_or (α * (x i.castSucc : ℕ)) (α * (d n : ℝ))
    rw [← mul_add, ← hsum] at hadd
    rcases hadd with h | h
    · exact (add_le_add_right (hfrac n).1 _).trans_eq h.symm
    · -- Wrapping around 1 would move backwards by at least the whole interval width.
      have hu := (hfrac n).2
      rw [Nat.cast_sub hr, Nat.cast_one, sub_div, div_self hr'.ne'] at hu
      have hnear := near i.castSucc i.succ
      dsimp only [phase] at hnear
      linarith only [hnear, h, hu]
  have advance (i : Fin (k + 1)) : phase (x 0) + (i : ℕ) * ε ≤ phase (x i) := by
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      rw [Fin.val_castSucc] at ih
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [ih, step i]
  have hlen : 1 ≤ (k : ℝ) * (r * ε) := by
    rw [← div_le_iff₀ (mul_pos hr' hε), one_div]
    exact Nat.le_ceil _
  have hwidth : 1 / (r : ℝ) ≤ (k : ℝ) * ε :=
    (div_le_iff₀ hr').2 (by linarith only [hlen])
  have hlast := advance (Fin.last k)
  simp only [Fin.val_last] at hlast
  linarith only [hlast, hwidth, near (Fin.last k) 0]

/-- **$r$-accessibility for colorings of the positive integers.** Let $r$ be a natural number. A set
$D$ of natural numbers is $r$-accessible when every element of $D$ is positive, $r \ge 1$, and for
every coloring $c$ of the positive integers with the colors $0, 1, \dots, r - 1$ and every natural
number $k \ge 1$ there are positive integers $x_0, \dots, x_{k-1}$ that are monochromatic for $c$
and form a $D$-diffsequence: $x_{i+1} - x_i \in D$, the difference taken in the integers, for every
$i$ with $i + 1 < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public def IsRAccessible (r : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
    ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
      ∃ x : Fin k → ℕ+,
        IsMonochromatic c x ∧ IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))

/-- **Characterization of $r$-accessible sets.** Let $r$ be a natural number and $D$ a set of
natural numbers. Then $D$ is $r$-accessible if and only if every element of $D$ is positive,
$r \ge 1$, and for every coloring $c$ of the positive integers with the colors $0, 1, \dots, r - 1$
and every natural number $k \ge 1$ there are positive integers $x_0, \dots, x_{k-1}$ that are
monochromatic for $c$ and form a $D$-diffsequence: $x_{i+1} - x_i \in D$, the difference taken in
the integers, for every $i$ with $i + 1 < k$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem isRAccessible_iff (r : ℕ) (D : Set ℕ) :
    IsRAccessible r D ↔ D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
      ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
        ∃ x : Fin k → ℕ+,
          IsMonochromatic c x ∧ IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ)) :=
  Iff.rfl

/-- **Sets containing their own long diffsequences are 2-accessible.** Let $D$ be a set of
positive integers. If for every $k \ge 1$ there are positive integers $x_1, \dots, x_k$, all in
$D$, that form a $D$-diffsequence, then $D$ is $2$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 2. -/
public theorem two_accessible_of_internal_diffsequences (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0)
    (hseq : ∀ k : ℕ, 1 ≤ k → ∃ x : Fin k → ℕ+,
      (∀ i, (x i : ℕ) ∈ D) ∧
        IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))) :
    IsRAccessible 2 D := by
  classical
  refine ⟨hD, by decide, ?_⟩
  intro c k hk
  obtain ⟨x, hx, hdiff⟩ := hseq k hk
  by_cases h : ∀ a : ℕ+, ∃ i, c (a + x i) = c a
  · -- Follow same-colored steps whose sizes are terms of the internal sequence.
    choose step hstep using h
    let walk : ℕ → ℕ+ := Nat.rec 1 (fun _ a => a + x (step a))
    have hcolor (n : ℕ) : c (walk n) = c 1 := by
      induction n with
      | zero => rfl
      | succ n ih => exact (hstep (walk n)).trans ih
    refine ⟨fun i => walk i, fun i j => (hcolor i).trans (hcolor j).symm, ?_⟩
    intro i hi
    exact ⟨_, hx (step (walk i)), by simp [walk, PNat.add_coe]⟩
  · -- All terms of this translate have the unique color different from that of its base.
    push Not at h
    obtain ⟨a, ha⟩ := h
    refine ⟨fun i => a + x i, ?_, ?_⟩
    · intro i j
      change c (a + x i) = c (a + x j)
      have hi := ha i
      have hj := ha j
      omega
    · intro i hi
      obtain ⟨d, hd, heq⟩ := hdiff i hi
      exact ⟨d, hd, by simpa [PNat.add_coe] using heq⟩

/-- **Accessibility with more colors implies accessibility with fewer.** Let $D$ be a set of
natural numbers and let $r, s$ be natural numbers with $1 \le r \le s$. If $D$ is
$s$-accessible, then $D$ is $r$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem IsRAccessible.mono (D : Set ℕ) {r s : ℕ} (h : IsRAccessible s D)
    (hr : 1 ≤ r) (hrs : r ≤ s) : IsRAccessible r D := by
  rcases h with ⟨hD, _, hs⟩
  refine ⟨hD, hr, ?_⟩
  intro c k hk
  obtain ⟨x, hx, hdiff⟩ := hs (fun n => Fin.castLE hrs (c n)) k hk
  refine ⟨x, ?_, hdiff⟩
  intro i j
  exact Fin.castLE_inj.mp (hx i j)

/-- **Multiples of $d$ in an accessible set.** Let $d \ge 1$ and $r$ be natural numbers and let $A$
be a set of natural numbers. If $A$ is $rd$-accessible, then the set $\{a \in A : d \mid a\}$ of
members of $A$ divisible by $d$ is $r$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 11(ii). -/
public theorem accessible_divisible_subset (A : Set ℕ) (d r : ℕ)
    (hd : 0 < d) (hA : IsRAccessible (r * d) A) :
    IsRAccessible r {a : ℕ | a ∈ A ∧ a % d = 0} := by
  obtain ⟨hpos, hrd, hseq⟩ := hA
  refine ⟨fun _ ha => hpos ha.1, Nat.pos_of_mul_pos_right hrd, ?_⟩
  intro c k hk
  let residue (n : ℕ+) : Fin d := ⟨(n : ℕ) % d, Nat.mod_lt _ hd⟩
  obtain ⟨x, hx, hdiff⟩ := hseq (fun n => finProdFinEquiv (c n, residue n)) k hk
  have hpair (i j : Fin k) := Prod.mk.inj (finProdFinEquiv.injective (hx i j))
  refine ⟨x, fun i j => (hpair i j).1, ?_⟩
  intro i hi
  obtain ⟨a, ha, hgap⟩ := hdiff i hi
  have hmod : Nat.ModEq d (x ⟨i, by omega⟩) (x ⟨i + 1, hi⟩) :=
    congrArg Fin.val (hpair _ _).2
  refine ⟨a, ⟨ha, Nat.mod_eq_zero_of_dvd ?_⟩, hgap⟩
  exact Int.natCast_dvd_natCast.mp (hgap ▸ hmod.dvd)

/-- **Accessible sets.** A set $D$ of natural numbers is accessible if it is $r$-accessible for
every natural number $r \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public def IsAccessible (D : Set ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → IsRAccessible r D

/-- **Accessibility means $r$-accessibility for every $r \ge 1$.** A set $D$ of natural numbers
is accessible if and only if it is $r$-accessible for every natural number $r \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem isAccessible_iff (D : Set ℕ) :
    IsAccessible D ↔ ∀ r : ℕ, 1 ≤ r → IsRAccessible r D :=
  Iff.rfl

/-- **Lacunary sequence.** A sequence $(m_n)_{n \ge 0}$ of natural numbers is lacunary when
$m_n > 0$ for every $n$ and there is a real number $\lambda > 1$ such that
$m_{n+1} \ge \lambda m_n$ for every $n \ge 0$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary sequence). -/
public def IsLacunary (m : ℕ → ℕ) : Prop :=
  (∀ n, 0 < m n) ∧ ∃ q : ℝ, 1 < q ∧
    ∀ n, (m (n + 1) : ℝ) ≥ q * (m n : ℝ)

/-- **Characterization of lacunary sequences.** A sequence $(m_n)_{n \ge 0}$ of natural numbers
is lacunary if and only if $m_n > 0$ for every $n$ and there is a real number $q > 1$ such that
$m_{n+1} \ge q \, m_n$ for every $n \ge 0$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary sequence). -/
public theorem isLacunary_iff (m : ℕ → ℕ) :
    IsLacunary m ↔ (∀ n, 0 < m n) ∧ ∃ q : ℝ, 1 < q ∧
      ∀ n, (m (n + 1) : ℝ) ≥ q * (m n : ℝ) :=
  Iff.rfl

/-- **Lacunary set.** A set $D$ of natural numbers is lacunary when $D = \{m_n : n \ge 0\}$ for
some lacunary sequence $(m_n)_{n \ge 0}$ of natural numbers.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary set). -/
public def IsLacunarySet (D : Set ℕ) : Prop :=
  ∃ m : ℕ → ℕ, IsLacunary m ∧ D = Set.range m

/-- **Characterization of lacunary sets.** A set $D$ of natural numbers is lacunary if and only
if there is a lacunary sequence $(m_n)_{n \ge 0}$ of natural numbers with
$D = \{m_n : n \ge 0\}$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary set). -/
public theorem isLacunarySet_iff (D : Set ℕ) :
    IsLacunarySet D ↔ ∃ m : ℕ → ℕ, IsLacunary m ∧ D = Set.range m :=
  Iff.rfl

/-- **Minimal system.** Let $X$ be a compact metric space and $T$ a homeomorphism of $X$. The
system $(X, T)$ is minimal when there is no closed set $K \subseteq X$ that is nonempty, different
from $X$ and invariant, meaning $T(K) = K$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (topological dynamical system, minimal). -/
public def IsMinimalSystem {X : Type*} [MetricSpace X] [CompactSpace X]
    (T : X ≃ₜ X) : Prop :=
  ¬ ∃ K : Set X, IsClosed K ∧ K.Nonempty ∧ K ≠ Set.univ ∧ T '' K = K

/-- **Characterization of minimal systems.** Let $X$ be a compact metric space and
$T \colon X \to X$ a homeomorphism. Then $T$ is minimal if and only if there is no closed set
$K \subseteq X$ with $K \ne \emptyset$, $K \ne X$ and $T(K) = K$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (topological dynamical system, minimal). -/
public theorem isMinimalSystem_iff {X : Type*} [MetricSpace X] [CompactSpace X]
    (T : X ≃ₜ X) :
    IsMinimalSystem T ↔
      ¬ ∃ K : Set X, IsClosed K ∧ K.Nonempty ∧ K ≠ Set.univ ∧ T '' K = K :=
  Iff.rfl

/-- **Iterated preimage.** For a homeomorphism $T$ of a topological space $X$, an integer $s$ and
a subset $U \subseteq X$, the iterated preimage $T^{-s} U$ is defined as the preimage
$(T^s)^{-1}(U)$ of $U$ under the $s$-th power $T^s$ of $T$ in the group of homeomorphisms of $X$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def iteratePreimage {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)
    (s : ℤ) (U : Set X) : Set X :=
  (T ^ s) ⁻¹' U

/-- **Iterated preimage as a preimage under a power.** For a homeomorphism $T$ of a topological
space $X$, an integer $s$ and a subset $U \subseteq X$, the iterated preimage $T^{-s} U$ is the
preimage $(T^s)^{-1}(U)$ of $U$ under the $s$-th power $T^s$ of $T$ in the group of
homeomorphisms of $X$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem iteratePreimage_eq {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)
    (s : ℤ) (U : Set X) : iteratePreimage T s U = (T ^ s) ⁻¹' U :=
  rfl

/-- **Sets of $\ell$-topological recurrence.** Let $\ell$ be a natural number. A set $D$ of
natural numbers is a set of $\ell$-topological recurrence when every element of $D$ is positive
and, for every compact metric space $X$, every minimal homeomorphism $T \colon X \to X$ and
every nonempty open set $U \subseteq X$, there is $d \in D$ such that
$\bigcap_{j=0}^{\ell} T^{-jd}(U)$ is nonempty, where $T^{-jd}(U)$ is the preimage of $U$ under
the $jd$-th iterate of $T$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsLTopologicalRecurrence (ℓ : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧
    ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
      IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
        ∃ d ∈ D, (⋂ j : Fin (ℓ + 1),
          iteratePreimage T (((j : ℕ) : ℤ) * (d : ℤ)) U).Nonempty

/-- **Characterization of $\ell$-topological recurrence.** Let $\ell$ be a natural number and $D$
a set of natural numbers. Then $D$ is a set of $\ell$-topological recurrence if and only if every
element of $D$ is positive and, for every compact metric space $X$, every minimal homeomorphism
$T \colon X \to X$ and every nonempty open set $U \subseteq X$, there is $d \in D$ such that
$\bigcap_{j=0}^{\ell} T^{-jd}(U)$ is nonempty, where $T^{-jd}(U)$ is the preimage of $U$ under
the $jd$-th iterate of $T$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isLTopologicalRecurrence_iff (ℓ : ℕ) (D : Set ℕ) :
    IsLTopologicalRecurrence ℓ D ↔ D ⊆ Set.Ioi 0 ∧
      ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∃ d ∈ D, (⋂ j : Fin (ℓ + 1),
            iteratePreimage T (((j : ℕ) : ℤ) * (d : ℤ)) U).Nonempty :=
  Iff.rfl

/-- **Sets of topological recurrence.** A set $D$ of natural numbers is a set of topological
recurrence when it is a set of $\ell$-topological recurrence for $\ell = 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsTopologicalRecurrence (D : Set ℕ) : Prop :=
  IsLTopologicalRecurrence 1 D

/-- **Topological recurrence is $1$-topological recurrence.** A set $D$ of natural numbers is a
set of topological recurrence if and only if it is a set of $\ell$-topological recurrence for
$\ell = 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isTopologicalRecurrence_iff (D : Set ℕ) :
    IsTopologicalRecurrence D ↔ IsLTopologicalRecurrence 1 D :=
  Iff.rfl

/-- **Sets of multiple topological recurrence.** A set $D$ of natural numbers is a set of multiple
topological recurrence when it is a set of $\ell$-topological recurrence for every natural number
$\ell \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsMultipleTopologicalRecurrence (D : Set ℕ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → IsLTopologicalRecurrence ℓ D

/-- **Characterization of multiple topological recurrence.** A set $D$ of natural numbers is a set
of multiple topological recurrence if and only if $D$ is a set of $\ell$-topological recurrence for
every natural number $\ell \ge 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isMultipleTopologicalRecurrence_iff (D : Set ℕ) :
    IsMultipleTopologicalRecurrence D ↔
      ∀ ℓ : ℕ, 1 ≤ ℓ → IsLTopologicalRecurrence ℓ D :=
  Iff.rfl

/-- **Chromatically intersective sets.** A set $D$ of natural numbers is chromatically
intersective if every element of $D$ is positive and, for every natural number $r \ge 1$ and
every coloring of the positive integers with $r$ colors, there are positive integers $a$ and $b$
of the same color whose difference $a - b$, computed in the integers, lies in $D$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13(iv). -/
public def IsChromaticallyIntersective (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ ∀ (r : ℕ), 1 ≤ r → ∀ c : ℕ+ → Fin r,
    ∃ a b : ℕ+, c a = c b ∧
      ∃ d ∈ D, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = (d : ℤ)

/-- **Characterization of chromatically intersective sets.** A set $D$ of natural numbers is
chromatically intersective if and only if every element of $D$ is positive and, for every
natural number $r \ge 1$ and every coloring of the positive integers with $r$ colors, there are
positive integers $a$ and $b$ of the same color whose difference $a - b$, computed in the
integers, lies in $D$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13(iv). -/
public theorem isChromaticallyIntersective_iff (D : Set ℕ) :
    IsChromaticallyIntersective D ↔
      D ⊆ Set.Ioi 0 ∧ ∀ (r : ℕ), 1 ≤ r → ∀ c : ℕ+ → Fin r,
        ∃ a b : ℕ+, c a = c b ∧
          ∃ d ∈ D, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = (d : ℤ) :=
  Iff.rfl

/-- **Positive Fibonacci set.** The positive Fibonacci set is $\{F_n : n \ge 2\}$, where the
Fibonacci numbers are $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. Equivalently, it is the
set $\{1, 2, 3, 5, 8, \dots\}$ of positive Fibonacci numbers, each counted once.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1. -/
public def positiveFibonacciSet : Set ℕ :=
  {d | ∃ n : ℕ, 2 ≤ n ∧ d = Nat.fib n}

/-- **Membership in the positive Fibonacci set.** Write $F_n$ for the $n$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. A natural number $d$ belongs to the positive Fibonacci set if and
only if $d = F_n$ for some natural number $n \ge 2$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1. -/
public theorem mem_positiveFibonacciSet_iff (d : ℕ) :
    d ∈ positiveFibonacciSet ↔ ∃ n : ℕ, 2 ≤ n ∧ d = Nat.fib n :=
  Iff.rfl

/-- **Even Fibonacci set.** Let $F_m$ denote the $m$-th Fibonacci number, with $F_0 = 0$ and
$F_1 = 1$. The even Fibonacci set is $\{F_{3n+3} : n \ge 0\}$; its first terms are
$2, 8, 34, \dots$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2. -/
public def evenFibonacciSet : Set ℕ :=
  {d | ∃ n : ℕ, d = Nat.fib (3 * n + 3)}

/-- **Membership in the even Fibonacci set.** Write $F_m$ for the $m$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$. A natural number $d$ belongs to the even Fibonacci set if and only if
$d = F_{3n+3}$ for some natural number $n$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2. -/
public theorem mem_evenFibonacciSet_iff (d : ℕ) :
    d ∈ evenFibonacciSet ↔ ∃ n : ℕ, d = Nat.fib (3 * n + 3) :=
  Iff.rfl

namespace accessible_union_partition

/-- A monochromatic sequence starting at `a` and taking `m` steps with gaps in `D`. -/
private def StartsAt {r : ℕ} (D : Set ℕ) (c : ℕ+ → Fin r) (a : ℕ+) (m : ℕ) : Prop :=
  ∃ x : Fin (m + 1) → ℕ+, x 0 = a ∧ (∀ i, c (x i) = c a) ∧
    IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))

private theorem prepend {r m : ℕ} {D : Set ℕ} {c : ℕ+ → Fin r} {a b : ℕ+}
    (hab : c a = c b) {d : ℕ} (hd : d ∈ D) (hgap : (b : ℤ) - (a : ℤ) = d)
    (hb : StartsAt D c b m) : StartsAt D c a (m + 1) := by
  obtain ⟨x, hx, hc, hdiff⟩ := hb
  refine ⟨Fin.cons a x, rfl, ?_, ?_⟩
  · exact Fin.forall_fin_succ.mpr ⟨rfl, fun i => (hc i).trans hab.symm⟩
  · intro i hi
    cases i with
    | zero =>
      refine ⟨d, hd, ?_⟩
      change (x 0 : ℤ) - (a : ℤ) = d
      rwa [hx]
    | succ i => exact hdiff i (by omega)

/-- A coloring forbidding a fixed sequence length can be refined to forbid even a single gap. -/
private theorem exists_gap_coloring {D : Set ℕ} (hpos : D ⊆ Set.Ioi 0) (h : ¬ IsAccessible D) :
    ∃ s > 0, ∃ f : ℕ+ → Fin s, ∀ a b, f a = f b → ∀ d ∈ D, (b : ℤ) - (a : ℤ) ≠ d := by
  classical
  obtain ⟨r, hr, c, k, hk, hbad⟩ :
      ∃ r, 1 ≤ r ∧ ∃ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k ∧
        ¬ ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧
          IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ)) := by
    by_contra! hall
    exact h fun r hr => ⟨hpos, hr, hall r hr⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- Count steps, so zero steps are attainable at every point via the singleton sequence.
  let rank (a : ℕ+) : Fin (k + 1) :=
    ⟨Nat.findGreatest (StartsAt D c a) k, Nat.lt_succ_of_le (Nat.findGreatest_le _)⟩
  have attains (a : ℕ+) : StartsAt D c a (rank a) := by
    apply Nat.findGreatest_spec (Nat.zero_le k)
    exact ⟨fun _ => a, rfl, fun _ => rfl, fun i hi => by omega⟩
  have below (a : ℕ+) : (rank a : ℕ) < k := by
    apply lt_of_le_of_ne (Nat.le_of_lt_succ (rank a).isLt)
    intro heq
    obtain ⟨x, _, hc, hdiff⟩ := heq ▸ attains a
    exact hbad ⟨x, fun i j => (hc i).trans (hc j).symm, hdiff⟩
  refine ⟨r * (k + 1), Nat.mul_pos hr (Nat.succ_pos _),
    fun a => finProdFinEquiv (c a, rank a), ?_⟩
  intro a b heq d hd hgap
  obtain ⟨hcolor, hrank⟩ := Prod.mk.inj (finProdFinEquiv.injective heq)
  -- Prepending the gap gives one more step than the common rank allows.
  have hstep := prepend hcolor hd hgap (attains b)
  have hle : (rank b : ℕ) + 1 ≤ rank a := Nat.le_findGreatest (below b) hstep
  rw [hrank] at hle
  omega

end accessible_union_partition

/-- **One part of an accessible union is accessible.** Let $D$, $D_1$ and $D_2$ be sets of
natural numbers with $D = D_1 \cup D_2$. If $D$ is accessible, then $D_1$ is accessible or $D_2$
is accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 3. -/
public theorem accessible_union_partition (D D₁ D₂ : Set ℕ)
    (hD : D = D₁ ∪ D₂) (hacc : IsAccessible D) :
    IsAccessible D₁ ∨ IsAccessible D₂ := by
  classical
  subst D
  have hpos := (hacc 1 le_rfl).1
  by_contra! ⟨h₁, h₂⟩
  obtain ⟨r, hr, c₁, hc₁⟩ := accessible_union_partition.exists_gap_coloring
    (Set.Subset.trans Set.subset_union_left hpos) h₁
  obtain ⟨s, hs, c₂, hc₂⟩ := accessible_union_partition.exists_gap_coloring
    (Set.Subset.trans Set.subset_union_right hpos) h₂
  obtain ⟨x, hx, hdiff⟩ := (hacc (r * s) (Nat.mul_pos hr hs)).2.2
    (fun a => finProdFinEquiv (c₁ a, c₂ a)) 2 (by decide)
  obtain ⟨d, hd, hgap⟩ := hdiff 0 (by decide)
  obtain ⟨heq₁, heq₂⟩ := Prod.mk.inj (finProdFinEquiv.injective (hx 0 1))
  rcases hd with hd | hd
  · exact hc₁ _ _ heq₁ d hd hgap
  · exact hc₂ _ _ heq₂ d hd hgap

end

end MetaMathlibExt
