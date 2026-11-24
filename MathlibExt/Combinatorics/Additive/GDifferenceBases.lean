/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Difference bases and bounded difference multiplicities

A positive difference determines the order of its representing pair. Counting such pairs in a
minimum difference basis for an interval gives the lower bound of Schmutz and Tait.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Difference representation function.** For a finite subset $A$ of an abelian group $G$ and
an element $x \in G$, the difference representation function $r_{A-A}(x)$ is the number of
ordered pairs $(a, a') \in A \times A$ with $a - a' = x$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public def subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (x : G) :
    ℕ :=
  ((A ×ˢ A).filter fun p => p.1 - p.2 = x).card

/-- **Products of difference bases.** Let $G_1, G_2$ be abelian groups, $g_1, g_2 \in \mathbb{N}$,
and $A_1 \subseteq G_1$, $A_2 \subseteq G_2$ finite sets. If every element of $G_1$ equals $a - a'$
for at least $g_1$ ordered pairs $(a, a') \in A_1 \times A_1$, and every element of $G_2$ equals
$a - a'$ for at least $g_2$ ordered pairs $(a, a') \in A_2 \times A_2$, then every element of
$G_1 \times G_2$ equals $z - z'$ for at least $g_1 g_2$ ordered pairs
$(z, z') \in (A_1 \times A_2) \times (A_1 \times A_2)$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem subRepCount_prod_ge {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂]
    [DecidableEq G₁] [DecidableEq G₂] (g₁ g₂ : ℕ) (A₁ : Finset G₁) (A₂ : Finset G₂)
    (h₁ : ∀ x, g₁ ≤ subRepCount A₁ x) (h₂ : ∀ x, g₂ ≤ subRepCount A₂ x) :
    ∀ x : G₁ × G₂, g₁ * g₂ ≤ subRepCount (A₁ ×ˢ A₂) x := by
  rintro ⟨x₁, x₂⟩
  let R₁ := (A₁ ×ˢ A₁).filter fun p => p.1 - p.2 = x₁
  let R₂ := (A₂ ×ˢ A₂).filter fun p => p.1 - p.2 = x₂
  -- Regroup two coordinate representations into one representation in the product group.
  let regroup := (Equiv.prodProdProdComm G₁ G₁ G₂ G₂).toEmbedding
  have hincl : (R₁ ×ˢ R₂).map regroup ⊆
      ((A₁ ×ˢ A₂) ×ˢ (A₁ ×ˢ A₂)).filter (fun p => p.1 - p.2 = (x₁, x₂)) := by
    intro p hp
    obtain ⟨⟨⟨a, a'⟩, ⟨b, b'⟩⟩, hab, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hma, hxa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hmb, hxb⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha, ha'⟩ := Finset.mem_product.mp hma
    obtain ⟨hb, hb'⟩ := Finset.mem_product.mp hmb
    change ((a, b), (a', b')) ∈ _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
        Finset.mem_product.mpr ⟨ha', hb'⟩⟩, Prod.ext hxa hxb⟩
  calc
    g₁ * g₂ ≤ subRepCount A₁ x₁ * subRepCount A₂ x₂ := Nat.mul_le_mul (h₁ x₁) (h₂ x₂)
    _ ≤ _ := by
      simpa only [Finset.card_map, Finset.card_product, R₁, R₂, subRepCount] using
        Finset.card_le_card hincl

/-- **The $g$-difference basis number.** For a finite set $A \subseteq \mathbb{Z}$ and
$x \in \mathbb{Z}$, write $r_{A-A}(x)$ for the number of ordered pairs $(a, a') \in A \times A$
with $a - a' = x$. For natural numbers $g$ and $n$, a finite set $A \subseteq \mathbb{Z}$ is a
$g$-difference basis for $[n] = \{1, \dots, n\}$ if $r_{A-A}(x) \ge g$ for every $x \in [n]$, and
$\eta_g(n)$ is the least size of such a set.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public noncomputable def diffBasisNumber (g n : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset ℤ, A.card = k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x}

/-- **Difference basis number of an abelian group.** For an abelian group $G$ and
$g \in \mathbb{N}$, a $g$-difference basis of $G$ is a finite set $A \subseteq G$ such that every
$x \in G$ equals $a - a'$ for at least $g$ ordered pairs $(a, a') \in A \times A$. The difference
basis number $\eta_g(G)$ is the least size of a $g$-difference basis of $G$, and $0$ if $G$ has
none.

There is no $g$-difference basis when $G$ is infinite and $g \ge 1$, or when $G$ is finite and
$g > |G|$, since each element is $a - a'$ for at most $|A| \le |G|$ pairs; in these cases the
value $0$ is a convention. When $G$ is finite and $g \le |G|$, the set $A = G$ is a
$g$-difference basis, so $\eta_g(G)$ is a true minimum. This is the paper's $\eta_g(S)$ with
$S = G$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 3. -/
public noncomputable def groupDiffBasisNumber (g : ℕ) (G : Type*) [AddCommGroup G]
    [DecidableEq G] : ℕ :=
  sInf {k | ∃ A : Finset G, A.card = k ∧ ∀ x : G, g ≤ subRepCount A x}

/-- **Maximal sets with bounded difference multiplicities.** For a finite set
$A \subseteq \mathbb{Z}$ and $x \in \mathbb{Z}$, write $r_{A-A}(x)$ for the number of ordered
pairs $(a, a') \in A \times A$ with $a - a' = x$. For natural numbers $g$ and $n$, $\alpha_g(n)$
is the largest size of a set $A \subseteq [n] = \{1, \dots, n\}$ with $r_{A-A}(x) \le g$ for
every nonzero integer $x$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 4. -/
public noncomputable def boundedDiffSetNumber (g n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℤ, A ⊆ Finset.Icc (1 : ℤ) n ∧ A.card = k ∧
    ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g}

/-- **Representations of zero as a difference.** For every finite subset $A$ of an abelian
group, $r_{A-A}(0) = |A|$: the number of ordered pairs $(a, a') \in A \times A$ with
$a - a' = 0$ equals the number of elements of $A$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem subRepCount_zero {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    subRepCount A 0 = A.card := by
  rw [← Finset.diag_card A, Finset.diag_eq_filter]
  simp only [subRepCount, sub_eq_zero]

private theorem two_le_card_of_subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {x : G} (hx : x ≠ 0) (h : 1 ≤ subRepCount A x) : 2 ≤ A.card := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hpx⟩ := hp
  have hne : p.1 ≠ p.2 := fun he => hx (by rw [← hpx, he, sub_self])
  exact Finset.one_lt_card.mpr ⟨p.1, h1, p.2, h2, hne⟩

/-- **The value $\eta_1(1) = 2$.** Let $\eta_1(1)$ be the least size of a finite set
$A \subseteq \mathbb{Z}$ containing elements $a, a'$ with $a - a' = 1$. Then $\eta_1(1) = 2$: such a
set needs two elements, and $\{0, 1\}$ is one.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem diffBasisNumber_one_one : diffBasisNumber 1 1 = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset ℤ, A.card = k ∧
      ∀ x ∈ Finset.Icc (1 : ℤ) (1 : ℕ), 1 ≤ subRepCount A x} := by
    refine ⟨{0, 1}, by decide, fun x hx => ?_⟩
    have : x = 1 := by simp at hx; omega
    subst this
    decide
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount one_ne_zero (hA 1 (by simp))

/-- **Difference basis number of $\mathbb{Z}/3\mathbb{Z}$.** The least size
$\eta_1(\mathbb{Z}/3\mathbb{Z})$ of a set $A \subseteq \mathbb{Z}/3\mathbb{Z}$ such that every
element of $\mathbb{Z}/3\mathbb{Z}$ is a difference $a - a'$ of two elements of $A$ equals $2$:
the set $\{0, 1\}$ has differences $0, 1, 2$, and one element is not enough.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 3. -/
public theorem groupDiffBasisNumber_one_zmod_three : groupDiffBasisNumber 1 (ZMod 3) = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset (ZMod 3), A.card = k ∧
      ∀ x : ZMod 3, 1 ≤ subRepCount A x} := ⟨{0, 1}, by decide, by decide⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount (by decide) (hA 1)

/-- **Trivial upper bound for sets with bounded difference multiplicities.** For natural numbers
$g$ and $n$, let $\alpha_g(n)$ be the largest size of a set $A \subseteq [n] = \{1, \dots, n\}$
such that every nonzero integer $x$ is the difference $a - a'$ of at most $g$ ordered pairs
$(a, a') \in A \times A$. Then $\alpha_g(n) \le n$, since these sets are subsets of $[n]$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_le (g n : ℕ) : boundedDiffSetNumber g n ≤ n := by
  refine csSup_le ⟨0, ∅, by simp, by simp, by simp [subRepCount]⟩ ?_
  rintro k ⟨A, hA, rfl, -⟩
  simpa using Finset.card_le_card hA

/-- **The value $\alpha_g(1) = 1$.** For natural numbers $g$ and $n$, let $\alpha_g(n)$ be the
largest size of a set $A \subseteq \{1, \dots, n\}$ such that every nonzero integer $x$ is the
difference $a - a'$ of at most $g$ ordered pairs $(a, a') \in A \times A$. Then for every natural
number $g$ we have $\alpha_g(1) = 1$: the singleton $\{1\}$ has no nonzero differences.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_one (g : ℕ) : boundedDiffSetNumber g 1 = 1 := by
  refine le_antisymm (boundedDiffSetNumber_le g 1) (le_csSup ⟨1, ?_⟩ ?_)
  · rintro k ⟨A, hA, rfl, -⟩
    simpa using Finset.card_le_card hA
  · refine ⟨{1}, by simp, rfl, fun x hx => ?_⟩
    have : subRepCount ({1} : Finset ℤ) x = 0 := by
      simp [subRepCount, Finset.filter_singleton, Ne.symm hx]
    omega

/-- For any natural numbers $g,n$, there is a finite set $A \subseteq \mathbb Z$ of size
$\eta_g(n)$, the interval difference basis number, such that each integer $1 \le x \le n$
has at least $g$ representations $x=a-a'$ by ordered pairs $(a,a') \in A \times A$. -/
public theorem diffBasisNumber_le_succ_mul.exists_min_basis (g n : ℕ) :
    ∃ A : Finset ℤ, A.card = diffBasisNumber g n ∧
      ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x := by
  apply Nat.sInf_mem (s := {k | ∃ A : Finset ℤ, A.card = k ∧
    ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x})
  let A := Finset.Icc (0 : ℤ) (n + g)
  refine ⟨A.card, A, rfl, fun x hx => ?_⟩
  obtain ⟨hx₁, hxn⟩ := Finset.mem_Icc.mp hx
  -- Each y in [0, g) gives a distinct representation (y + x, y).
  calc
    g = (Finset.Ico (0 : ℤ) g).card := by simp
    _ ≤ subRepCount A x := by
      apply Finset.card_le_card_of_injOn (fun y : ℤ => (y + x, y))
      · intro y hy
        obtain ⟨hy₀, hyg⟩ := Finset.mem_Ico.mp hy
        simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        omega
      · intro a _ b _ hab
        exact congrArg Prod.snd hab

/-- Repeat a finite set in disjoint translates, preserving each difference in every copy. -/
private theorem exists_disjoint_translates {A : Finset ℤ} (hA : A.Nonempty) (g : ℕ) :
    ∃ B : Finset ℤ, B.card = g * A.card ∧
      ∀ x : ℤ, 1 ≤ subRepCount A x → g ≤ subRepCount B x := by
  let lo := A.min' hA
  let hi := A.max' hA
  let d := hi - lo + 1
  have hwidth : hi < lo + d := by dsimp [d]; omega
  have hd : 0 ≤ d := by
    have h : lo ≤ hi := A.min'_le_max' hA
    omega
  let shift (p : ℕ × ℤ) := p.2 + (p.1 : ℤ) * d
  let S := Finset.range g ×ˢ A
  -- The step exceeds the diameter, so each copy lies strictly before the next.
  have hlt {i j : ℕ} {a b : ℤ} (hij : i < j) (ha : a ∈ A) (hb : b ∈ A) :
      shift (i, a) < shift (j, b) := by
    have ha' : a ≤ hi := A.le_max' a ha
    have hb' : lo ≤ b := A.min'_le b hb
    have hstep := mul_le_mul_of_nonneg_right
      (show (i : ℤ) + 1 ≤ (j : ℤ) by omega) hd
    rw [add_mul, one_mul] at hstep
    change a + (i : ℤ) * d < b + (j : ℤ) * d
    omega
  have hinj : Set.InjOn shift S := by
    rintro ⟨i, a⟩ hp ⟨j, b⟩ hq he
    have ha := (Finset.mem_product.mp (show (i, a) ∈ S from hp)).2
    have hb := (Finset.mem_product.mp (show (j, b) ∈ S from hq)).2
    have hij : i = j := le_antisymm
      (le_of_not_gt fun h => (hlt h hb ha).ne he.symm)
      (le_of_not_gt fun h => (hlt h ha hb).ne he)
    subst j
    exact congrArg (Prod.mk i) (add_right_cancel he)
  refine ⟨S.image shift, ?_, fun x hx => ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
  · obtain ⟨⟨a, b⟩, hp⟩ := Finset.card_pos.mp hx
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    rw [← Finset.card_range g]
    apply Finset.card_le_card_of_injOn (fun i => (shift (i, a), shift (i, b)))
    · intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mk_mem_product ?_ ?_, ?_⟩
      · exact Finset.mem_image_of_mem shift (Finset.mk_mem_product hi ha)
      · exact Finset.mem_image_of_mem shift (Finset.mk_mem_product hi hb)
      · simpa [shift] using hab
    · intro i hi j hj he
      exact congrArg Prod.fst <|
        hinj (Finset.mk_mem_product hi ha) (Finset.mk_mem_product hj ha) (congrArg Prod.fst he)

/-- **Comparing $g$-difference bases with difference bases.** For natural numbers $g$ and $n$,
let $\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, n\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. If $n > 1$ and $g \ge 1$, then
$\eta_1(n) \le \eta_g(n) \le g\,\eta_1(n)$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 2 (`integers-2025-A77-cor-2`). -/
public theorem diffBasisNumber_one_le_and_le_mul (g n : ℕ) (hn : 1 < n) (hg : 1 ≤ g) :
    diffBasisNumber 1 n ≤ diffBasisNumber g n ∧ diffBasisNumber g n ≤ g * diffBasisNumber 1 n := by
  constructor
  · obtain ⟨A, hcard, hA⟩ := diffBasisNumber_le_succ_mul.exists_min_basis g n
    exact Nat.sInf_le ⟨A, hcard, fun x hx => hg.trans (hA x hx)⟩
  · obtain ⟨A, hcard, hA⟩ := diffBasisNumber_le_succ_mul.exists_min_basis 1 n
    have h1 : (1 : ℤ) ∈ Finset.Icc 1 (n : ℤ) :=
      Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hn.le⟩
    have htwo := two_le_card_of_subRepCount one_ne_zero (hA 1 h1)
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨B, hBcard, hB⟩ := exists_disjoint_translates hne g
    exact Nat.sInf_le ⟨B, hBcard.trans (congrArg (g * ·) hcard), fun x hx => hB x (hA x hx)⟩

namespace sqrt_two_mul_le_diffBasisNumber_div_sqrt

private theorem mul_le_card_choose_two {g n : ℕ} (A : Finset ℤ)
    (hA : ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x) :
    n * g ≤ A.card.choose 2 := by
  let I := Finset.Icc (1 : ℤ) n
  calc
    n * g = ∑ _x ∈ I, g := by simp [I]
    _ ≤ ∑ x ∈ I, subRepCount A x := Finset.sum_le_sum hA
    _ = ((A ×ˢ A).filter fun p => p.1 - p.2 ∈ I).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ ((A ×ˢ A).filter fun p => p.2 < p.1).card := by
      apply Finset.card_le_card (Finset.monotone_filter_right _ ?_)
      intro p _ hp
      have := (Finset.mem_Icc.mp hp).1
      omega
    _ = A.card.choose 2 := Finset.card_product_filter_lt (α := ℤᵒᵈ) (s := A)

end sqrt_two_mul_le_diffBasisNumber_div_sqrt

open sqrt_two_mul_le_diffBasisNumber_div_sqrt in
/-- **Trivial lower bound for difference bases of an interval.** Let $g, n \in \mathbb{N}$ with
$n > 1$, and let $\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that
every $x \in \{1, \dots, n\}$ equals $a - a'$ for at least $g$ ordered pairs
$(a, a') \in A \times A$. Then $\eta_g(n) / \sqrt{n} \ge \sqrt{2g}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 1 (`integers-2025-A77-lem-1`). -/
public theorem sqrt_two_mul_le_diffBasisNumber_div_sqrt (g n : ℕ) (hn : 1 < n) :
    Real.sqrt (2 * g) ≤ (diffBasisNumber g n : ℝ) / Real.sqrt n := by
  obtain ⟨A, hcard, hA⟩ := diffBasisNumber_le_succ_mul.exists_min_basis g n
  have hcount := mul_le_card_choose_two A hA
  rw [Nat.choose_two_right] at hcount
  have hsq : 2 * g * n ≤ A.card ^ 2 := calc
    2 * g * n = 2 * (n * g) := by ac_rfl
    _ ≤ A.card * (A.card - 1) := by omega
    _ ≤ A.card ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le ..)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  rw [le_div_iff₀ (Real.sqrt_pos.2 hn'), ← Real.sqrt_mul (by positivity),
    Real.sqrt_le_iff, ← hcard]
  exact ⟨by positivity, by exact_mod_cast hsq⟩

end

/-- **Rédei–Rényi difference basis.** Let $n \ge 1$ and $k = \lceil \sqrt{n} \rceil$. The set
of integers $B_n = \{1, \dots, k - 1\} \cup \{k, 2k, \dots, k^2, (k + 1)k\}$ has $2k$ elements,
and every $x \in \{1, \dots, n\}$ is a difference $b - b'$ of two elements of $B_n$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 2 (`integers-2025-A77-lem-2`). -/
public theorem redeiRenyi_diffBasis (n : ℕ) (hn : 0 < n) :
    let k : ℕ := ⌈Real.sqrt n⌉₊
    let B : Finset ℤ :=
      Finset.Icc 1 ((k : ℤ) - 1) ∪ (Finset.Icc (1 : ℤ) (k + 1)).image (· * (k : ℤ))
    B.card = 2 * k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, 1 ≤ subRepCount B x := by
  let k : ℕ := ⌈Real.sqrt n⌉₊
  let L := Finset.Icc (1 : ℤ) ((k : ℤ) - 1)
  let M := Finset.Icc (1 : ℤ) ((k : ℤ) + 1)
  let R := M.image (· * (k : ℤ))
  change (L ∪ R).card = 2 * k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, 1 ≤ subRepCount (L ∪ R) x
  have hceil : Real.sqrt (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hkreal : (0 : ℝ) < k := (Real.sqrt_pos.2 hnreal).trans_le hceil
  have hk : (0 : ℤ) < k := by exact_mod_cast hkreal
  have hsq : (n : ℤ) ≤ (k : ℤ) * (k : ℤ) := by
    exact_mod_cast (show (n : ℝ) ≤ (k : ℝ) * (k : ℝ) from calc
      (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnreal.le).symm
      _ ≤ (k : ℝ) * (k : ℝ) := mul_le_mul hceil hceil (Real.sqrt_nonneg _) hkreal.le)
  constructor
  · have hdis : Disjoint L R := Finset.disjoint_left.2 fun a ha hb => by
      have ha' := (Finset.mem_Icc.1 ha).2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
      have hlow := mul_le_mul_of_nonneg_right (Finset.mem_Icc.1 hj).1 hk.le
      rw [one_mul] at hlow
      omega
    have hinj : Function.Injective fun j : ℤ => j * (k : ℤ) :=
      fun _ _ heq => mul_right_cancel₀ hk.ne' heq
    rw [Finset.card_union_of_disjoint hdis, show R.card = M.card from
      Finset.card_image_of_injective M hinj]
    dsimp [L, M]
    rw [Int.card_Icc, Int.card_Icc]
    omega
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.1 hx
    let q := x / (k : ℤ)
    let r := x % (k : ℤ)
    have hr₀ : 0 ≤ r := Int.emod_nonneg _ hk.ne'
    have hrk : r < (k : ℤ) := Int.emod_lt_of_pos _ hk
    have hdiv : q * (k : ℤ) + r = x := by
      simpa [q, r, add_comm] using Int.emod_add_ediv_mul x (k : ℤ)
    have hq₀ : 0 ≤ q := Int.ediv_nonneg (by omega) hk.le
    have hqk : q ≤ (k : ℤ) := le_of_mul_le_mul_right
      ((show q * (k : ℤ) ≤ x by omega).trans (hx₂.trans hsq)) hk
    have hmultiple (j : ℤ) (hj₁ : 1 ≤ j) (hj₂ : j ≤ (k : ℤ) + 1) :
        j * (k : ℤ) ∈ L ∪ R :=
      Finset.mem_union_right L (Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨hj₁, hj₂⟩, rfl⟩)
    -- The complement of the remainder is in the short interval unless it equals k.
    have hright : (k : ℤ) - r ∈ L ∪ R := by
      by_cases hzero : r = 0
      · simpa [hzero] using hmultiple 1 le_rfl (by omega)
      · exact Finset.mem_union_left R (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hleft := hmultiple (q + 1) (by omega) (by omega)
    change 1 ≤ (((L ∪ R) ×ˢ (L ∪ R)).filter (fun p : ℤ × ℤ => p.1 - p.2 = x)).card
    apply Nat.succ_le_of_lt
    refine Finset.card_pos.2 ⟨((q + 1) * (k : ℤ), (k : ℤ) - r), ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hleft, hright⟩, ?_⟩
    change (q + 1) * (k : ℤ) - ((k : ℤ) - r) = x
    rw [add_mul, one_mul]
    omega

end MetaMathlibExt
