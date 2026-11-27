/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Rat.Place
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Local-global facts about the rationals

Two inputs to the proof of the Hasse–Minkowski theorem over `ℚ`, stated with the places
`Rat.Place` and completions `Rat.Place.CompletedField` of `ℚ`:

* `Rat.isSquare_of_isSquare_real_of_forall_isSquare_padic`: a rational number that is a square in
  `ℝ` and in every `ℚ_[p]` is a square in `ℚ`; the arithmetic core is
  `Rat.isSquare_of_pos_of_forall_even_padicValRat`.
* `Rat.Place.exists_forall_norm_sub_lt` and `Rat.Place.denseRange_embedding_pi`: weak
  approximation for `ℚ`, the density of `ℚ` in a finite product of its completions.

Sources: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, Theorem 11.7, p. 2, and the case `n = 2` of the proof of Theorem 11.12, p. 4;
J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), Theorem 7.20 and the
remark after it, p. 114.
-/

public section

namespace Rat

/-- **A positive rational number with even valuations is a square.** Let $r \in \mathbb{Q}$ with
$r > 0$, and suppose that the $p$-adic valuation $v_p(r)$ is even for every prime $p$. Then $r$
is a square in $\mathbb{Q}$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, proof of Theorem 11.12, case $n = 2$, p. 4. -/
theorem isSquare_of_pos_of_forall_even_padicValRat {r : ℚ} (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p r)) : IsSquare r := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hval : ∀ p : ℕ, p.Prime → padicValRat p r =
      (r.num.natAbs.factorization p : ℤ) - (r.den.factorization p : ℤ) := by
    intro p hp
    rw [padicValRat_def, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    simp [padicValInt]
  have key : ∀ p : ℕ, p.Prime →
      Even (r.num.natAbs.factorization p) ∧ Even (r.den.factorization p) := by
    intro p hp
    have he := h p hp
    rw [hval p hp] at he
    by_cases hpn : p ∣ r.num.natAbs
    · have hpd : ¬p ∣ r.den := fun hpd =>
        Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpn, hpd⟩ r.reduced
      rw [Nat.factorization_eq_zero_of_not_dvd hpd] at he ⊢
      exact ⟨by simpa using he, ⟨0, rfl⟩⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn] at he ⊢
      exact ⟨⟨0, rfl⟩, by simpa using he⟩
  have hsqn : IsSquare r.num.natAbs :=
    Nat.isSquare_iff_even_factorization.mpr fun p hp => (key p hp).1
  have hsqd : IsSquare r.den :=
    Nat.isSquare_iff_even_factorization.mpr fun p hp => (key p hp).2
  refine Rat.isSquare_iff.mpr ⟨?_, hsqd⟩
  obtain ⟨m, hm⟩ := hsqn
  exact ⟨m, by rw [← Int.natAbs_of_nonneg hnum.le, hm]; push_cast; ring⟩

/-- **A rational number that is a square at every place is a square.** Let $r \in \mathbb{Q}$. If
$r$ is a square in $\mathbb{R}$ and in $\mathbb{Q}_p$ for every prime $p$, then $r$ is a square in
$\mathbb{Q}$.

For $r \neq 0$: being a square in $\mathbb{R}$, $r > 0$, and being a square in $\mathbb{Q}_p$, $r$
has even $p$-adic valuation, so `Rat.isSquare_of_pos_of_forall_even_padicValRat` applies; $r = 0$
is a square.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, proof of Theorem 11.12, case $n = 2$, p. 4. -/
theorem isSquare_of_isSquare_real_of_forall_isSquare_padic {r : ℚ} (hreal : IsSquare (r : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], IsSquare (r : ℚ_[p])) : IsSquare r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, by simp⟩
  have hpos : 0 < r := by
    obtain ⟨s, hs⟩ := hreal
    have h0 : (0 : ℝ) ≤ r := by rw [hs]; exact mul_self_nonneg s
    exact lt_of_le_of_ne (by exact_mod_cast h0) (Ne.symm hr0)
  refine isSquare_of_pos_of_forall_even_padicValRat hpos fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := hpadic p
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hr0 (by exact_mod_cast (show (r : ℚ_[p]) = 0 by simpa using hs))
  have hv := congrArg Padic.valuation hs
  rw [Padic.valuation_ratCast, Padic.valuation_mul hs0 hs0] at hv
  exact ⟨_, hv⟩

namespace Place

/-- **The absolute value at a rational place is nontrivial.** For every place $v$ of
$\mathbb{Q}$, the absolute value $|\cdot|_v$ takes a value different from $1$ at some nonzero
rational number: $|2|_\infty = 2$, and $|p|_p = 1/p$ at a prime $p$. -/
theorem absoluteValue_isNontrivial (v : Place) : v.absoluteValue.IsNontrivial := by
  cases v with
  | infinite =>
    refine ⟨2, two_ne_zero, ?_⟩
    rw [absoluteValue_infinite_apply]
    norm_num
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    refine ⟨prime.1, by exact_mod_cast prime.2.ne_zero, ?_⟩
    rw [← embedding_norm_eq_absoluteValue]
    change ‖((prime.1 : ℚ) : ℚ_[prime.1])‖ ≠ 1
    rw [Rat.cast_natCast, Padic.norm_p]
    have h1 : (1 : ℝ) < prime.1 := by exact_mod_cast prime.2.one_lt
    exact ne_of_lt (inv_lt_one_of_one_lt₀ h1)

/-- **Distinct rational places have inequivalent absolute values.** If $v \neq w$ are places of
$\mathbb{Q}$, then the absolute values $|\cdot|_v$ and $|\cdot|_w$ are not equivalent. -/
theorem absoluteValue_not_isEquiv {v w : Place} (h : v ≠ w) :
    ¬v.absoluteValue.IsEquiv w.absoluteValue := by
  intro hvw
  obtain ⟨u, -, hu⟩ := exists_unique_place_equiv v.absoluteValue v.absoluteValue_isNontrivial
  exact h ((hu v (AbsoluteValue.IsEquiv.refl _)).trans (hu w hvw).symm)

/-- **Weak approximation for the rationals.** Let $S$ be a finite set of places of $\mathbb{Q}$
and, for each $v \in S$, let $x_v \in \mathbb{Q}_v$. Then for every $\epsilon > 0$ there is
$x \in \mathbb{Q}$ with $|x - x_v|_v < \epsilon$ for every $v \in S$, where $|\cdot|_v$ is the
norm of the completion $\mathbb{Q}_v$: the usual absolute value on $\mathbb{Q}_\infty = \mathbb{R}$
and the $p$-adic norm on $\mathbb{Q}_p$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, Theorem 11.7, p. 2; J. S. Milne, *Algebraic Number Theory*, course notes,
version 3.08 (2020), Theorem 7.20 and the remark after it, p. 114. -/
theorem exists_forall_norm_sub_lt (S : Finset Place) (x : (v : S) → CompletedField v.1)
    {ε : ℝ} (hε : 0 < ε) : ∃ q : ℚ, ∀ v : S, ‖embedding v.1 q - x v‖ < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose r hr using fun v : S =>
    (Metric.denseRange_iff.mp (denseRange_embedding v.1)) (x v) (ε / 2) hε2
  have hd := AbsoluteValue.denseRange_algebraMap_pi (F := ℚ) (ι := S)
    (v := fun v => v.1.absoluteValue) (fun v => v.1.absoluteValue_isNontrivial)
    (fun v w hvw => absoluteValue_not_isEquiv fun h => hvw (Subtype.ext h))
  obtain ⟨q, hq⟩ := Metric.denseRange_iff.mp hd
    (fun v => WithAbs.toAbs v.1.absoluteValue (r v)) (ε / 2) hε2
  refine ⟨q, fun v => ?_⟩
  have h1 : v.1.absoluteValue (q - r v) < ε / 2 := by
    have hv := lt_of_le_of_lt (dist_le_pi_dist _ _ v) hq
    have e1 : (algebraMap ℚ ((w : S) → WithAbs w.1.absoluteValue) q) v =
        WithAbs.toAbs v.1.absoluteValue q := rfl
    rwa [e1, dist_comm, dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hv
  calc ‖embedding v.1 q - x v‖
      ≤ ‖embedding v.1 q - embedding v.1 (r v)‖ + ‖embedding v.1 (r v) - x v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = v.1.absoluteValue (q - r v) + dist (x v) (embedding v.1 (r v)) := by
        rw [← map_sub, embedding_norm_eq_absoluteValue, dist_comm, dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add h1 (hr v)
    _ = ε := add_halves ε

/-- **The rationals are dense in a finite product of their completions.** Let $S$ be a finite set
of places of $\mathbb{Q}$. The image of $\mathbb{Q}$ in $\prod_{v \in S} \mathbb{Q}_v$ under the
diagonal map $q \mapsto (q)_{v \in S}$ is dense in the product topology.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture
notes, Lecture 11, Theorem 11.7, p. 2; J. S. Milne, *Algebraic Number Theory*, course notes,
version 3.08 (2020), Theorem 7.20 and the remark after it, p. 114. -/
theorem denseRange_embedding_pi (S : Finset Place) :
    DenseRange (fun (q : ℚ) (v : S) => embedding v.1 q) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨q, hq⟩ := exists_forall_norm_sub_lt S x (half_pos hε)
  refine ⟨q, lt_of_le_of_lt ((dist_pi_le_iff (half_pos hε).le).mpr fun v => ?_)
    (half_lt_self hε)⟩
  rw [dist_comm, dist_eq_norm]
  exact (hq v).le

end Place

end Rat
