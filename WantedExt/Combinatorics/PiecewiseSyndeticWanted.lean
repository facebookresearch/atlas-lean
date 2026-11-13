/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat

/-!
# Piecewise syndetic sets in `ℕ^t`

Statements from Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*,
INTEGERS 24 (2024), Article A2.

Points of `ℕ^t` are functions `Fin t → ℕ`. A subcube of size `m^t` is a lattice
cube `∏ i, [a i, a i + m)` with side `m`. A set `C` is `d`-dense in a cube `M` when
every subcube of `M` of size `d^t` meets `C` (Lemma 1 of the paper). A set `C` is
piecewise syndetic when, for some fixed `d`, `C + [0, d]^t` contains arbitrarily
large subcubes (Proof 1 of Theorem 2 of the paper).

Here `ℕ` contains `0`, while the paper works in positive integers; translating by
the all-ones vector identifies the two settings and preserves all notions above.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lattice cube.** For $t, m \in \mathbb{N}$ and $a \in \mathbb{N}^t$, the lattice cube
with least corner $a$ and side $m$ is the set of points $x \in \mathbb{N}^t$ such that
$a_i \le x_i < a_i + m$ for every coordinate $i$; it is a subcube of size $m^t$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (subcubes of `N^t` of size `m^t`). -/
def latticeCube {t : ℕ} (a : Fin t → ℕ) (m : ℕ) : Set (Fin t → ℕ) :=
  Set.univ.pi fun i => Set.Ico (a i) (a i + m)

/-- **Membership in a lattice cube.** For $t, m \in \mathbb{N}$ and $a, x \in \mathbb{N}^t$,
the point $x$ lies in the lattice cube with least corner $a$ and side $m$ if and only if
$a_i \le x_i < a_i + m$ for every coordinate $i$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (subcubes of `N^t` of size `m^t`). -/
theorem mem_latticeCube {t : ℕ} {a x : Fin t → ℕ} {m : ℕ} :
    x ∈ latticeCube a m ↔ ∀ i, a i ≤ x i ∧ x i < a i + m := by
  simp [latticeCube]

/-- **Lattice cube of side one.** For $t \in \mathbb{N}$ and $a \in \mathbb{N}^t$, the lattice
cube with least corner $a$ and side $1$ is the singleton $\{a\}$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (subcubes of `N^t` of size `m^t`). -/
theorem latticeCube_one {t : ℕ} (a : Fin t → ℕ) : latticeCube a 1 = {a} := by
  ext x
  simp only [mem_latticeCube, Set.mem_singleton_iff, funext_iff]
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    rw [h i]
    omega

/-- **Density in subcubes.** Let $d \in \mathbb{N}$ and let $C, M \subseteq \mathbb{N}^t$. The set
$C$ is $d$-dense in $M$ when every subcube of $\mathbb{N}^t$ of side $d$ that is contained in $M$
meets $C$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (definition of `m_{i-1}`-dense in `M'`). -/
def IsDenseInCubes {t : ℕ} (d : ℕ) (C M : Set (Fin t → ℕ)) : Prop :=
  ∀ b : Fin t → ℕ, latticeCube b d ⊆ M → (latticeCube b d ∩ C).Nonempty

/-- **Density one means containment.** For sets $C, M \subseteq \mathbb{N}^t$, the set $C$ is
$1$-dense in $M$ if and only if $M \subseteq C$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (definition of `m_{i-1}`-dense in `M'`, with `m_0 = 1`). -/
theorem isDenseInCubes_one_iff {t : ℕ} {C M : Set (Fin t → ℕ)} :
    IsDenseInCubes 1 C M ↔ M ⊆ C := by
  simp only [IsDenseInCubes, latticeCube_one, Set.singleton_subset_iff,
    Set.singleton_inter_nonempty]
  exact Iff.rfl

/-- **Piecewise syndetic set.** Let $t \in \mathbb{N}$. A set $A \subseteq \mathbb{N}^t$ is
piecewise syndetic if there is $d \in \mathbb{N}$ such that, writing
$[0, d] = \{0, 1, \dots, d\}$, for every $m \in \mathbb{N}$ the set
$A + [0, d]^t = \{y + z : y \in A,\ z \in [0, d]^t\}$ contains a lattice cube of side $m$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Proof 1 of Theorem 2 (meaning of piecewise syndetic). -/
def IsPiecewiseSyndetic {t : ℕ} (A : Set (Fin t → ℕ)) : Prop :=
  ∃ d : ℕ, ∀ m : ℕ, ∃ a : Fin t → ℕ,
    latticeCube a m ⊆ {x | ∃ y ∈ A, ∃ z ∈ latticeCube 0 (d + 1), x = y + z}

/-- **The whole space is piecewise syndetic.** For every $t \in \mathbb{N}$, the whole space
$\mathbb{N}^t$ is piecewise syndetic.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Proof 1 of Theorem 2 (meaning of piecewise syndetic). -/
theorem isPiecewiseSyndetic_univ {t : ℕ} : IsPiecewiseSyndetic (Set.univ : Set (Fin t → ℕ)) :=
  ⟨0, fun _ => ⟨0, fun x _ => ⟨x, Set.mem_univ _, 0,
    by rw [zero_add, latticeCube_one]; exact Set.mem_singleton _, (add_zero x).symm⟩⟩⟩

/-- **The empty set is not piecewise syndetic.** For every $t \in \mathbb{N}$, the empty
subset of $\mathbb{N}^t$ is not piecewise syndetic.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Proof 1 of Theorem 2 (meaning of piecewise syndetic). -/
theorem not_isPiecewiseSyndetic_empty {t : ℕ} :
    ¬ IsPiecewiseSyndetic (∅ : Set (Fin t → ℕ)) := by
  rintro ⟨d, h⟩
  obtain ⟨a, ha⟩ := h 1
  obtain ⟨y, hy, -⟩ := ha (by rw [latticeCube_one]; exact Set.mem_singleton a)
  exact hy

/-- **A color class is dense in a subcube (Brown, Lemma 1).** Let $t, r \in \mathbb{N}$ and let
$1 = m_0 < m_1 < m_2 < \cdots$ be a strictly increasing sequence of natural numbers. Let $M$ be a
subcube of $\mathbb{N}^t$ of side $m_r$, and let $c$ be a coloring of $\mathbb{N}^t$ by natural
numbers with $1 \le c(x) \le r$ for every $x \in M$. Then for some color $i$ with $1 \le i \le r$
there is a subcube $M' \subseteq M$ of side $m_i$ in which the class of color $i$ is
$m_{i-1}$-dense.

The paper fixes $t \ge 1$ and $r \ge 1$; both are dropped, since $t = 0$ holds trivially and
$r = 0$ admits no coloring of the nonempty cube $M$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 1 (`integers-2024-A2-lem-1`). -/
public theorem_wanted exists_subcube_isDenseInCubes_colorClass (t : ℕ) (m : ℕ → ℕ)
    (hm0 : m 0 = 1) (hm : StrictMono m) (r : ℕ) (a : Fin t → ℕ) (c : (Fin t → ℕ) → ℕ)
    (hc : ∀ x ∈ latticeCube a (m r), c x ∈ Set.Icc 1 r) :
    ∃ i ∈ Set.Icc 1 r, ∃ a' : Fin t → ℕ, latticeCube a' (m i) ⊆ latticeCube a (m r) ∧
      IsDenseInCubes (m (i - 1)) {x | c x = i} (latticeCube a' (m i))

/-- **A color class is dense in a large subcube (Brown, Lemma 2).** Let $r, t \in \mathbb{N}$ and
let $f : \mathbb{N} \to \mathbb{N}$. There is $A \in \mathbb{N}$ such that for every coloring of
$\mathbb{N}^t$ with $r$ colors there are natural numbers $d \ge 1$ and $m > f(d)$, a color $j$, and
a subcube $M$ of side $m$ with $M \subseteq [1, A]^t$ in which the class of color $j$ is
$d$-dense. Here $[1, A]^t$ is the set of points $x$ with $1 \le x_i \le A$ for every coordinate $i$.

The paper's "(a smallest)" is omitted: it follows from existence. Only the restriction of the
coloring to $[1, A]^t$ matters.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Lemma 2 (`integers-2024-A2-lem-2`). -/
public theorem_wanted exists_cube_bound_isDenseInCubes (r t : ℕ) (f : ℕ → ℕ) :
    ∃ A : ℕ, ∀ c : (Fin t → ℕ) → Fin r, ∃ d m : ℕ, 1 ≤ d ∧ f d < m ∧ ∃ j : Fin r,
      ∃ a : Fin t → ℕ, latticeCube a m ⊆ latticeCube (fun _ => 1) A ∧
        IsDenseInCubes d {x | c x = j} (latticeCube a m)

/-- **Piecewise syndeticity is partition regular.** Let $A \subseteq \mathbb{N}^t$ be piecewise
syndetic and let $A_1, \dots, A_r \subseteq \mathbb{N}^t$ with $A = A_1 \cup \dots \cup A_r$. Then
some $A_i$ is piecewise syndetic.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Theorem 1 (`integers-2024-A2-thm-1`). -/
public theorem_wanted IsPiecewiseSyndetic.exists_of_eq_iUnion {t r : ℕ}
    {A : Set (Fin t → ℕ)} (hA : IsPiecewiseSyndetic A) (B : Fin r → Set (Fin t → ℕ))
    (hAB : A = ⋃ i, B i) : ∃ i, IsPiecewiseSyndetic (B i)

/-- **Gap size.** For a set $S \subseteq \mathbb{N}^t$, the gap size $\operatorname{gs}(S)$ is the
least $d \ge 1$ such that $S$ is $d$-dense in some subcube of $\mathbb{N}^t$ that contains $S$. If
no such $d$ exists (for instance when $S$ is unbounded, so that no subcube contains it), the value
is $0$.

For $t = 1$, the gap size of a finite set with at least two points is the largest difference
between consecutive elements, and a one-point set has gap size $1$ (Definition 1). The paper
defines $\operatorname{gs}$ only for finite sets; when $t \ge 1$, every finite set has positive gap
size.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Definition 5. -/
public noncomputable def cubeGapSize {t : ℕ} (S : Set (Fin t → ℕ)) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ ∃ (a : Fin t → ℕ) (m : ℕ), S ⊆ latticeCube a m ∧
    IsDenseInCubes d S (latticeCube a m)}

/-- **Density bounds the gap size.** Let $S \subseteq \mathbb{N}^t$, let $d \ge 1$, and let $M$ be a
subcube of $\mathbb{N}^t$ with $S \subseteq M$. If $S$ is $d$-dense in $M$, then the gap size of $S$
satisfies $\operatorname{gs}(S) \le d$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Definition 5 (and Proof 1 of Theorem 2, "hence `gs(S) ≤ d`"). -/
public theorem cubeGapSize_le_of_isDenseInCubes {t d m : ℕ} {S : Set (Fin t → ℕ)}
    {a : Fin t → ℕ} (hd : 0 < d) (hS : S ⊆ latticeCube a m)
    (hdense : IsDenseInCubes d S (latticeCube a m)) : cubeGapSize S ≤ d :=
  Nat.sInf_le ⟨hd, a, m, hS, hdense⟩

/-- **Finite sets in positive dimension have positive gap size.** Let $t \ge 1$. Every finite set
$S \subseteq \mathbb{N}^t$ has gap size $\operatorname{gs}(S) > 0$.

Indeed, $S$ lies in some subcube $[0, m)^t$, and it is vacuously $(m + 1)$-dense there, since no
subcube of side $m + 1$ fits inside.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Definition 5. -/
public theorem cubeGapSize_pos {t : ℕ} (ht : 1 ≤ t) (S : Finset (Fin t → ℕ)) :
    0 < cubeGapSize (S : Set (Fin t → ℕ)) := by
  set m := S.sup (fun x => Finset.univ.sup x) + 1
  have hS : (S : Set (Fin t → ℕ)) ⊆ latticeCube (fun _ => 0) m := by
    intro x hx
    simp only [latticeCube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, zero_add, true_implies]
    intro i
    refine ⟨Nat.zero_le _, Nat.lt_succ_of_le ?_⟩
    exact (Finset.le_sup (f := x) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun x => Finset.univ.sup x) (Finset.mem_coe.mp hx))
  have hdense : IsDenseInCubes (m + 1) (S : Set (Fin t → ℕ)) (latticeCube (fun _ => 0) m) := by
    intro b hb
    exfalso
    have i : Fin t := ⟨0, ht⟩
    have h1 := hb (show b ∈ latticeCube b (m + 1) by
      simp [latticeCube, Set.mem_pi])
    have h2 := hb (show (fun j => b j + m) ∈ latticeCube b (m + 1) by
      simp [latticeCube, Set.mem_pi])
    simp only [latticeCube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies] at h1 h2
    have := (h2 i).2
    omega
  have hne : {d : ℕ | 0 < d ∧ ∃ (a : Fin t → ℕ) (m : ℕ), (S : Set (Fin t → ℕ)) ⊆
      latticeCube a m ∧ IsDenseInCubes d (S : Set (Fin t → ℕ)) (latticeCube a m)}.Nonempty :=
    ⟨m + 1, Nat.succ_pos m, _, m, hS, hdense⟩
  exact (Nat.sInf_mem hne).1

/-- **Gap size of a singleton.** For every point $x \in \mathbb{N}^t$, the one-point set
$\lbrace x \rbrace$ has gap size $\operatorname{gs}(\lbrace x \rbrace) = 1$.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Definitions 1 and 5 ("If `|S| = 1`, we set `gs(S) = 1`"). -/
public theorem cubeGapSize_singleton {t : ℕ} (x : Fin t → ℕ) : cubeGapSize {x} = 1 := by
  have hmem : 1 ∈ {d : ℕ | 0 < d ∧ ∃ (a : Fin t → ℕ) (m : ℕ), ({x} : Set (Fin t → ℕ)) ⊆
      latticeCube a m ∧ IsDenseInCubes d {x} (latticeCube a m)} :=
    ⟨Nat.one_pos, x, 1, by rw [latticeCube_one],
      isDenseInCubes_one_iff.mpr (by rw [latticeCube_one])⟩
  apply le_antisymm (Nat.sInf_le hmem)
  have hne : {d : ℕ | 0 < d ∧ ∃ (a : Fin t → ℕ) (m : ℕ), ({x} : Set (Fin t → ℕ)) ⊆
      latticeCube a m ∧ IsDenseInCubes d {x} (latticeCube a m)}.Nonempty := ⟨1, hmem⟩
  exact (Nat.sInf_mem hne).1

/-- **Monochromatic sets that are large relative to their gap size.** Let $r, t \in \mathbb{N}$ with
$t \ge 1$, and let $f : \mathbb{N} \to \mathbb{N}$ be nondecreasing. There is $B \in \mathbb{N}$
such that for every coloring of $\mathbb{N}^t$ with $r$ colors there is a finite monochromatic set
$S \subseteq [1, B]^t$ with $|S| > f(\operatorname{gs}(S))$, where $\operatorname{gs}(S)$ is the gap
size of $S$ and $[1, B]^t$ is the set of points $x$ with $1 \le x_i \le B$ for every coordinate $i$.

The paper's "(a smallest)" is omitted: it follows from existence. Only the restriction of the
coloring to $[1, B]^t$ matters. The hypothesis $t \ge 1$ is the paper's; for $t = 0$ and $r \ge 1$
the statement fails when $f(1) \ge 1$, since the only point gives $|S| = 1 = \operatorname{gs}(S)$.
The paper's hypothesis $r \ge 1$ is dropped: for $r = 0$ there is no coloring and the statement
holds vacuously.

Source: Tom C. Brown, *Piecewise Syndetic Sets in `N^t` and `N^X`*, INTEGERS 24
(2024), Article A2, Theorem 2 (`integers-2024-A2-thm-2`). -/
public theorem_wanted exists_cube_bound_monochromatic_card_gt_gapSize (r t : ℕ) (ht : 1 ≤ t)
    (f : ℕ → ℕ) (hf : Monotone f) :
    ∃ B : ℕ, ∀ c : (Fin t → ℕ) → Fin r, ∃ j : Fin r, ∃ S : Finset (Fin t → ℕ),
      (S : Set (Fin t → ℕ)) ⊆ latticeCube (fun _ => 1) B ∧ (∀ x ∈ S, c x = j) ∧
        f (cubeGapSize (S : Set (Fin t → ℕ))) < S.card

end

end MetaMathlibExt
