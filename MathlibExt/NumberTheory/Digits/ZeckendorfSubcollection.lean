/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.Nat

/-!
# Counting a Zeckendorf subcollection

Replacing a nonzero expansion by the successor of its predecessor in a subcollection preserves
the set of represented integers strictly below its value. The two evaluations then identify
the same lower segment of coefficient functions with the counted set and with a natural interval.

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25.
  Section 2.2, Definition 6 and the order-preservation part of Theorem 5; Section 3.2,
  Definitions 20–21, Lemma 7, and Theorem 8 (Duality Formula).
  <https://math.colgate.edu/~integers/z25/z25.pdf>
* Sungkon Chang, *The weak converse of Zeckendorf’s theorem*, Research in Number Theory 7
  (2021), Article 48, Theorem 16 and Lemmas 3 and 37, credited in Theorem 5 above.
* Édouard Zeckendorf, *Représentation des nombres naturels par une somme des nombres de
  Fibonacci ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège 41
  (1972), pp. 179–182, for the classical representation theorem.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ascending lexicographic order.** For coefficient functions
$\mu, \nu \colon \mathbb{N} \to \mathbb{N}$ with finite support, $\mu <_a \nu$ means that there
is an index $k$ with $\mu_k < \nu_k$ and $\mu_j = \nu_j$ for all $j > k$: at the largest index
where they differ, $\mu$ is smaller.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def AscLexLT (μ ν : ℕ →₀ ℕ) : Prop :=
  ∃ k, μ k < ν k ∧ ∀ j, k < j → μ j = ν j

/-- **Immediate predecessor.** Let $E$ be a collection of finitely supported coefficient functions
$\mathbb N \to \mathbb N$, and let $<_a$ be the ascending lexicographic order. A finitely supported
coefficient function $\mu$ is the immediate predecessor of $\nu$ in $E$ if $\mu \in E$,
$\mu <_a \nu$, and every $\xi \in E$ with $\xi <_a \nu$ satisfies $\xi = \mu$ or $\xi <_a \mu$.
That is, $\mu$ is the largest element of $E$ that is $<_a \nu$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediatePredecessor (E : Set (ℕ →₀ ℕ)) (ν μ : ℕ →₀ ℕ) : Prop :=
  μ ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT ξ ν → ξ = μ ∨ AscLexLT ξ μ

/-- **Immediate successor.** Let $E$ be a collection of finitely supported coefficient functions
$\mathbb N \to \mathbb N$, and let $<_a$ be the ascending lexicographic order. A finitely supported
coefficient function $\nu$ is the immediate successor of $\mu$ in $E$ if $\nu \in E$,
$\mu <_a \nu$, and every $\xi \in E$ with $\mu <_a \xi$ satisfies $\xi = \nu$ or $\nu <_a \xi$.
That is, $\nu$ is the smallest element of $E$ that is $>_a \mu$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediateSuccessor (E : Set (ℕ →₀ ℕ)) (μ ν : ℕ →₀ ℕ) : Prop :=
  ν ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT μ ξ → ξ = ν ∨ AscLexLT ν ξ

/-- **Zeckendorf collections.** In Chang's one-based indexing, let $\beta^n$ be the basis
coefficient function with entry $1$ at index $n$, and for a coefficient function $\mu$ let
$\operatorname{res}_n(\mu)$ keep the entries of $\mu$ at indices $\le n$ and
$\operatorname{res}^n(\mu)$ keep those at indices $\ge n$, the other entries being $0$. A set $E$
of finitely supported coefficient functions $\mathbb N \to \mathbb N$ is a Zeckendorf collection
when it contains $0$ and $\beta^n$ for every $n \ge 1$, every $\mu \in E$ has only finitely many
elements of $E$ below it in the ascending lexicographic order $<_a$, and for every $\mu \in E$
and every immediate successor $\tilde\mu$ of $\mu$ in $E$ with $\tilde\mu \ne \beta^1 + \mu$
there is an index $n \ge 2$ such that $\operatorname{res}_{n-1}(\mu)$ is the immediate
predecessor of $\beta^n$ in $E$ and $\tilde\mu = \beta^n + \operatorname{res}^n(\mu)$.

Lean represents Chang's basis digit $\beta^n$ by `Finsupp.single (n - 1) 1` for $n \ge 1$.
The first basis digit is `Finsupp.single 0 1`, and a carry at Chang's index $n \ge 2$ occurs
at Lean index $m = n - 1 \ge 1$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsZeckendorfCollection (E : Set (ℕ →₀ ℕ)) : Prop :=
  0 ∈ E ∧ (∀ i, Finsupp.single i 1 ∈ E) ∧ (∀ μ ∈ E, {ν | ν ∈ E ∧ AscLexLT ν μ}.Finite) ∧
    ∀ μ ∈ E, ∀ ν, IsImmediateSuccessor E μ ν → ν ≠ Finsupp.single 0 1 + μ →
      ∃ m, 1 ≤ m ∧ IsImmediatePredecessor E (Finsupp.single m 1) (μ.filter (· < m)) ∧
        ν = Finsupp.single m 1 + μ.filter (m ≤ ·)

/-- **Evaluation of a coefficient function at an integer sequence.** For a sequence $H$ of
natural numbers and a finitely supported coefficient function
$\varepsilon \colon \mathbb{N} \to \mathbb{N}$, the evaluation of $\varepsilon$ at $H$ is the
natural number $\mathrm{eval}_H(\varepsilon) = \sum_{k \ge 0} \varepsilon_k H_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 1 (arXiv:2308.12872v1, Section 1). -/
public def zeckendorfEval (H : ℕ → ℕ) (ε : ℕ →₀ ℕ) : ℕ :=
  ε.sum fun k a => a * H k

namespace subcollectionLT_eval_eq_eval_bar

private abbrev Digits := ℕ →₀ ℕ

private theorem asc_iff {x y : Digits} : AscLexLT x y ↔ toColex x < toColex y := by
  simp only [AscLexLT, Finsupp.Colex.lt_iff, ofColex_toColex, and_comm]

private theorem below_pred {E : Set Digits} {x p z : Digits}
    (hp : IsImmediatePredecessor E x p) (hz : z ∈ E) :
    toColex z < toColex x ↔ toColex z ≤ toColex p := by
  constructor
  · intro h
    obtain rfl | h := hp.2.2 z hz (asc_iff.mpr h)
    · exact le_rfl
    · exact (asc_iff.mp h).le
  · exact fun h => h.trans_lt (asc_iff.mp hp.2.1)

private theorem below_succ {E : Set Digits} {x p z : Digits}
    (hx : IsImmediateSuccessor E p x) (hz : z ∈ E) :
    toColex z < toColex x ↔ toColex z ≤ toColex p := by
  constructor
  · intro h
    by_contra! h'
    obtain rfl | hxz := hx.2.2 z hz (asc_iff.mpr h')
    · exact (lt_irrefl _ h)
    · exact h.not_gt (asc_iff.mp hxz)
  · exact fun h => h.trans_lt (asc_iff.mp hx.2.1)

private theorem predecessor_exists {E : Set Digits} (hE : IsZeckendorfCollection E)
    {x : Digits} (hx : x ∈ E) (hx0 : x ≠ 0) : ∃ p, IsImmediatePredecessor E x p := by
  have h0 : toColex (0 : Digits) < toColex x :=
    lt_of_le_of_ne (Finsupp.toColex_monotone (zero_le : (0 : Digits) ≤ x))
      (toColex.injective.ne hx0.symm)
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image _ toColex (hE.2.2.1 x hx)
    ⟨0, hE.1, asc_iff.mpr h0⟩
  refine ⟨p, hp.1, hp.2, fun z hz hzx => ?_⟩
  exact (hmax z ⟨hz, hzx⟩).eq_or_lt.imp (fun he => toColex.injective he) asc_iff.mpr

private theorem succ_of_pred {E : Set Digits} {x p : Digits}
    (hx : x ∈ E) (hp : IsImmediatePredecessor E x p) : IsImmediateSuccessor E p x := by
  refine ⟨hx, hp.2.1, fun z hz hpz => ?_⟩
  have h := (below_pred hp hz).not.mpr (not_le.mpr (asc_iff.mp hpz))
  exact (le_of_not_gt h).eq_or_lt.imp (fun he => toColex.injective he.symm) asc_iff.mpr

private theorem eval_single (H : ℕ → ℕ) (k : ℕ) :
    zeckendorfEval H (Finsupp.single k 1) = H k := by
  simp [zeckendorfEval]

private theorem eval_add (H : ℕ → ℕ) (x y : Digits) :
    zeckendorfEval H (x + y) = zeckendorfEval H x + zeckendorfEval H y := by
  exact Finsupp.sum_add_index' (by simp) (by simp [add_mul])

private theorem weight_le_eval {H : ℕ → ℕ} {x : Digits} {k : ℕ} (hk : x k ≠ 0) :
    H k ≤ zeckendorfEval H x := by
  have h := Finsupp.single_le_sum x (g := fun i a => a * H i) (fun _ _ => Nat.zero_le _) k
  simp only [Finsupp.sum_single_index, zero_mul] at h
  exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk)).trans h

-- An integer smaller than the m-th weight can only have digits below index m.
private theorem below_single_of_eval_lt {H : ℕ → ℕ} (hmono : StrictMono H)
    {x : Digits} {m : ℕ} (h : zeckendorfEval H x < H m) :
    toColex x < toColex (Finsupp.single m 1) := by
  have hzero (k) (hk : m ≤ k) : x k = 0 := by
    by_contra hne
    exact h.not_ge ((hmono.monotone hk).trans (weight_le_eval hne))
  apply asc_iff.mp
  exact ⟨m, by simp [hzero m le_rfl], fun j hj => by simp [hzero j hj.le, hj.ne']⟩

-- Order agreement at p identifies the entire segment below its immediate successor.
private theorem eval_le_pred {E : Set Digits} {H : ℕ → ℕ} {x p : Digits}
    (hinj : Set.InjOn (zeckendorfEval H) E) (hp : IsImmediatePredecessor E x p)
    (ih : ∀ z ∈ E, toColex z < toColex p ↔ zeckendorfEval H z < zeckendorfEval H p)
    {z : Digits} (hz : z ∈ E) :
    toColex z < toColex x ↔ zeckendorfEval H z ≤ zeckendorfEval H p := by
  rw [below_pred hp hz, le_iff_lt_or_eq, le_iff_lt_or_eq, ih z hz, toColex_inj]
  exact or_congr_right ⟨congrArg _, hinj hz hp.1⟩

-- There is exactly one numerical step from the predecessor of a basis digit to its weight.
private theorem weight_eq_succ {E : Set Digits} {H : ℕ → ℕ} (hmono : StrictMono H)
    (hbij : Set.BijOn (zeckendorfEval H) E Set.univ) {m : ℕ} (hm : Finsupp.single m 1 ∈ E)
    {p : Digits} (hp : IsImmediatePredecessor E (Finsupp.single m 1) p)
    (ih : ∀ z ∈ E, toColex z < toColex p ↔ zeckendorfEval H z < zeckendorfEval H p) :
    H m = zeckendorfEval H p + 1 := by
  have hlt := (eval_le_pred hbij.injOn hp ih hm).not.mp (lt_irrefl _)
  rw [eval_single] at hlt
  obtain ⟨z, hz, he⟩ := hbij.surjOn (Set.mem_univ (zeckendorfEval H p + 1))
  by_contra hne
  have hsmall : zeckendorfEval H z < H m := by omega
  have := (eval_le_pred hbij.injOn hp ih hz).mp (below_single_of_eval_lt hmono hsmall)
  omega

private theorem eval_order {E : Set Digits} (hE : IsZeckendorfCollection E)
    {H : ℕ → ℕ} (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) E Set.univ) (x : Digits) (hx : x ∈ E) :
    ∀ z ∈ E, toColex z < toColex x ↔ zeckendorfEval H z < zeckendorfEval H x := by
  have hfirst : H 0 = 1 := by
    obtain ⟨z, _, hz⟩ := hbij.surjOn (Set.mem_univ 1)
    have hne : z ≠ 0 := by
      rintro rfl
      simp [zeckendorfEval] at hz
    obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hne
    have := (hmono.monotone (Nat.zero_le k)).trans (weight_le_eval (H := H)
      (Finsupp.mem_support_iff.mp hk))
    have := hpos 0
    omega
  -- Each successor either adds the first digit or carries a lower block into a basis digit.
  have wf := InvImage.wf (@toColex Digits) (wellFounded_lt (α := Colex Digits))
  induction x using wf.induction with
  | h x ih =>
    by_cases hx0 : x = 0
    · subst x
      intro z _
      simp [zeckendorfEval]
    obtain ⟨p, hp⟩ := predecessor_exists hE hx hx0
    have hpx := asc_iff.mp hp.2.1
    have hstep : zeckendorfEval H x = zeckendorfEval H p + 1 := by
      by_cases hs : x = Finsupp.single 0 1 + p
      · rw [hs, eval_add, eval_single, hfirst, Nat.add_comm]
      · obtain ⟨m, _, hlow, hcarry⟩ := hE.2.2.2 p hp.1 x (succ_of_pred hx hp) hs
        have hle : p.filter (· < m) ≤ p := by
          intro k
          by_cases hk : k < m <;> simp [hk]
        have hw := weight_eq_succ hmono hbij (hE.2.1 m) hlow
          (ih _ ((Finsupp.toColex_monotone hle).trans_lt hpx) hlow.1)
        have hsplit : p.filter (· < m) + p.filter (m ≤ ·) = p := by
          simpa using p.filter_add_filter_not (· < m)
        have he := congrArg (zeckendorfEval H) hsplit
        rw [eval_add] at he
        rw [hcarry, eval_add, eval_single, hw]
        omega
    intro z hz
    rw [hstep, Nat.lt_succ_iff]
    exact eval_le_pred hbij.injOn hp (ih _ hpx hp.1) hz

end subcollectionLT_eval_eq_eval_bar

open subcollectionLT_eval_eq_eval_bar in
set_option linter.unusedVariables false in
/-- **Reduction lemma for counting a subcollection.** Let $E \subseteq \tilde E$ be Zeckendorf
collections, and let $\tilde H$ be a strictly increasing sequence of positive integers such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde H_k$ is a bijection from $\tilde E$ onto
$\mathbb{N}$. For a natural number $x$ let $R(x)$ be the set of natural numbers $n < x$ of the
form $n = \sum_k \varepsilon_k \tilde H_k$ with $\varepsilon \in E$. Let $\mu \in \tilde E$ be
nonzero, suppose that $\mu$ has an immediate predecessor $\check\mu$ in $E$ (the largest element
of $E$ that is $<_a \mu$ in the ascending lexicographic order), and suppose that $\check\mu$ has
an immediate successor $\bar\mu$ in $E$ (the smallest element of $E$ that is $>_a \check\mu$).
Then $R(\sum_k \mu_k \tilde H_k) = R(\sum_k \bar\mu_k \tilde H_k)$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 7 (`integers-2025-A25-lem-7`; arXiv:2308.12872v1, Section 3.2, with the paper's
definition of `μ̌` and `μ̄` there). -/
public theorem subcollectionLT_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H' : ℕ → ℕ} (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ) {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E')
    (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc) (hb : IsImmediateSuccessor E μc μb) :
    {n : ℕ | n < zeckendorfEval H' μ ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n} =
      {n : ℕ | n < zeckendorfEval H' μb ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n} := by
  have hcut (z) (hz : z ∈ E) :
      zeckendorfEval H' z < zeckendorfEval H' μ ↔ zeckendorfEval H' z < zeckendorfEval H' μb := by
    rw [← eval_order hE' hmono' hpos' hbij' μ hμ z (hsub hz),
      ← eval_order hE' hmono' hpos' hbij' μb (hsub hb.1) z (hsub hz), below_pred hc hz,
      below_succ hb hz]
  ext n
  constructor
  · rintro ⟨hlt, z, hz, rfl⟩
    exact ⟨(hcut z hz).mp hlt, z, hz, rfl⟩
  · rintro ⟨hlt, z, hz, rfl⟩
    exact ⟨(hcut z hz).mpr hlt, z, hz, rfl⟩

/-- **Counting function of a subcollection.** For a set $E$ of finitely supported coefficient
functions $\mu : \mathbb{N} \to \mathbb{N}$, a sequence $H : \mathbb{N} \to \mathbb{N}$ and a
real number $x$, $z(x)$ is the number of natural numbers $n < x$ of the form
$n = \sum_k \mu_k H_k$ for some $\mu \in E$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1 and Section 3 (arXiv:2308.12872v1, Sections 1 and 3.2). -/
public noncomputable def subcollectionCount (E : Set (ℕ →₀ ℕ)) (H : ℕ → ℕ) (x : ℝ) : ℕ :=
  {n : ℕ | (n : ℝ) < x ∧ ∃ μ ∈ E, zeckendorfEval H μ = n}.ncard

open subcollectionLT_eval_eq_eval_bar in
/-- **Duality formula.** Let $E \subseteq \tilde E$ be Zeckendorf collections. Let $H$ and
$\tilde H$ be strictly increasing sequences of positive integers such that
$\mu \mapsto \sum_k \mu_k H_k$ is a bijection from $E$ onto $\mathbb N$ and
$\mu \mapsto \sum_k \mu_k \tilde H_k$ is a bijection from $\tilde E$ onto $\mathbb N$. For real
$x$, let $z(x)$ be the number of natural numbers $n < x$ of the form $n = \sum_k \nu_k \tilde H_k$
with $\nu \in E$. Let $\mu \in \tilde E$ be nonzero, let $\check\mu$ be the immediate predecessor
of $\mu$ in $E$ (the largest element of $E$ below $\mu$ in the ascending lexicographic order), and
let $\bar\mu$ be the immediate successor of $\check\mu$ in $E$. Then
$z\left(\sum_k \mu_k \tilde H_k\right) = \sum_k \bar\mu_k H_k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 8 (`integers-2025-A25-thm-8`; arXiv:2308.12872v1, Section 3.2). -/
public theorem subcollectionCount_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H H' : ℕ → ℕ} (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) E Set.univ) (hmono' : StrictMono H')
    (hpos' : ∀ k, 0 < H' k) (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ)
    {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E') (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc)
    (hb : IsImmediateSuccessor E μc μb) :
    subcollectionCount E H' (zeckendorfEval H' μ) = zeckendorfEval H μb := by
  unfold subcollectionCount
  simp only [Nat.cast_lt]
  rw [subcollectionLT_eval_eq_eval_bar hE hE' hsub hmono' hpos' hbij' hμ hμ0 hc hb]
  let S : Set (ℕ →₀ ℕ) := {z | z ∈ E ∧ toColex z < toColex μb}
  have hH := eval_order hE hmono hpos hbij μb hb.1
  have hH' (z : ℕ →₀ ℕ) (hz : z ∈ E) :=
    eval_order hE' hmono' hpos' hbij' μb (hsub hb.1) z (hsub hz)
  have hsmall : Set.BijOn (zeckendorfEval H) S (Set.Iio (zeckendorfEval H μb)) := by
    refine ⟨fun z hz ↦ (hH z hz.1).mp hz.2, hbij.injOn.mono (fun _ hz ↦ hz.1), ?_⟩
    intro n hn
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn (Set.mem_univ n)
    exact ⟨z, ⟨hz, (hH z hz).mpr hn⟩, rfl⟩
  have hlarge : Set.BijOn (zeckendorfEval H') S
      {n : ℕ | n < zeckendorfEval H' μb ∧ ∃ z ∈ E, zeckendorfEval H' z = n} := by
    refine ⟨?_, hbij'.injOn.mono (fun _ hz ↦ hsub hz.1), ?_⟩
    · intro z hz
      exact ⟨(hH' z hz.1).mp hz.2, z, hz.1, rfl⟩
    · rintro n ⟨hn, z, hz, rfl⟩
      exact ⟨z, ⟨hz, (hH' z hz).mpr hn⟩, rfl⟩
  rw [← hlarge.ncard_eq, hsmall.ncard_eq, Set.ncard_Iio_nat]

end

end MetaMathlibExt
