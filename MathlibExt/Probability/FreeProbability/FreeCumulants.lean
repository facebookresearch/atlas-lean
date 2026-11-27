/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.NoncrossingPartition.Small
public import MathlibExt.Probability.Distributions.SemicircleNoncrossingPairings

/-!
# Free cumulants and the R-transform

The free cumulants `κ₁, κ₂, …` of a moment sequence `m` are defined by the moment-cumulant formula
over noncrossing partitions,
`mₙ = ∑_{π ∈ NC(n)} ∏_{V ∈ π} κ_{|V|}` for `n ≥ 1`
(Anderson, Guionnet and Zeitouni (manuscript numbering), Definition 5.3.13, for the cumulants
`kₙ(a) = kₙ(a, …, a)` of a
single variable). The formula is triangular: the term for the one-block partition `1ₙ` is `κₙ`, and
every other noncrossing partition has blocks of size `< n`, so `κₙ` is determined recursively
(Lemma 5.3.14). The R-transform is the formal power series `R(z) = ∑_{n ≥ 0} κ_{n+1} zⁿ`
(Definition 5.3.22).

The semicircle law is the free Gaussian: its only nonzero free cumulant is `κ₂ = 1`, so its
R-transform is `R(z) = z` (Example 5.3.26). This is proved here from the count of noncrossing pair
partitions.

## Main definitions

* `MathlibExt.Probability.FreeProbability.freeCumulant m n`: the `n`-th free cumulant of the moment
  sequence `m : ℕ → ℂ`.
* `MathlibExt.Probability.FreeProbability.rTransform m`: the R-transform of `m`, as a formal power
  series.

## Main results

* `moment_eq_sum_noncrossing_prod_freeCumulant`: the moment-cumulant formula.
* `freeCumulant_one`: `κ₁ = m₁`.
* `freeCumulant_semicircle`: the free cumulants of the semicircle law are `κₙ = [n = 2]`.
* `rTransform_semicircle`: the R-transform of the semicircle law is `z`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
  pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §5.3.2:
  Definition 5.3.13,
  Lemma 5.3.14, Definition 5.3.22 and Example 5.3.26.
-/

@[expose] public section

open Finset NoncrossingPartition

namespace MathlibExt.Probability.FreeProbability

/-- **Free cumulants of a moment sequence** (Anderson, Guionnet and Zeitouni, *An Introduction to
Random Matrices* (manuscript numbering), Definition 5.3.13 and Lemma 5.3.14). For a moment sequence
`m : ℕ → ℂ`, `κₙ` is
defined recursively by solving the moment-cumulant formula
`mₙ = ∑_{π ∈ NC(n)} ∏_{V ∈ π} κ_{|V|}` for its one-block term:
`κₙ = mₙ - ∑_{π ∈ NC(n), π ≠ 1ₙ} ∏_{V ∈ π} κ_{|V|}`.
Every block of a partition `π ≠ 1ₙ` has fewer than `n` elements, so the recursion is well founded;
the guard `|V| < n` is always met. The value at `n = 0` is `m₀` and plays no role. -/
noncomputable def freeCumulant (m : ℕ → ℂ) (n : ℕ) : ℂ :=
  m n - ∑ π ∈ (univ : Finset (_root_.NoncrossingPartition n)).erase ⊤,
    ∏ V ∈ π.val.parts, if _h : V.card < n then freeCumulant m V.card else 0
termination_by n

/- Blocks of a noncrossing partition other than `1ₙ` have fewer than `n` elements. -/
theorem card_lt_of_mem_parts_of_ne_top {n : ℕ} {π : _root_.NoncrossingPartition n} (hπ : π ≠ ⊤)
    {V : Finset (Fin n)} (hV : V ∈ π.val.parts) : V.card < n := by
  refine lt_of_le_of_ne (by simpa using card_le_univ V) fun hcard => hπ ?_
  have hVuniv : V = univ := eq_univ_of_card V (by simpa using hcard)
  refine eq_indiscrete_of_forall_block_eq_univ π fun a => ?_
  rw [← hVuniv]
  exact π.val.part_eq_of_mem hV (by rw [hVuniv]; exact mem_univ a)

/-- **Moment-cumulant formula** (Anderson, Guionnet and Zeitouni, *An Introduction to Random
Matrices*, equation (5.3.5) for a single variable): for `n ≥ 1`,
`mₙ = ∑_{π ∈ NC(n)} ∏_{V ∈ π} κ_{|V|}`. -/
theorem moment_eq_sum_noncrossing_prod_freeCumulant (m : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    m n = ∑ π : _root_.NoncrossingPartition n, ∏ V ∈ π.val.parts, freeCumulant m V.card := by
  rw [← add_sum_erase _ _ (mem_univ (⊤ : _root_.NoncrossingPartition n))]
  have htop : ∏ V ∈ (⊤ : _root_.NoncrossingPartition n).val.parts, freeCumulant m V.card =
      freeCumulant m n := by
    change ∏ V ∈ (indiscrete n).val.parts, freeCumulant m V.card = _
    rw [indiscrete_parts_pos hn, prod_singleton, card_univ, Fintype.card_fin]
  have hrest : ∑ π ∈ (univ : Finset (_root_.NoncrossingPartition n)).erase ⊤,
      ∏ V ∈ π.val.parts, freeCumulant m V.card =
      ∑ π ∈ (univ : Finset (_root_.NoncrossingPartition n)).erase ⊤,
      ∏ V ∈ π.val.parts, if h : V.card < n then freeCumulant m V.card else 0 := by
    refine sum_congr rfl fun π hπ => prod_congr rfl fun V hV => ?_
    rw [dite_eq_left (card_lt_of_mem_parts_of_ne_top (ne_of_mem_erase hπ) hV)]
  rw [htop, hrest, freeCumulant]
  ring

/-- **The first free cumulant is the mean**, `κ₁ = m₁`: the only noncrossing partition of one point
is the one-block partition. -/
theorem freeCumulant_one (m : ℕ → ℂ) : freeCumulant m 1 = m 1 := by
  rw [freeCumulant]
  have : (univ : Finset (_root_.NoncrossingPartition 1)).erase ⊤ = ∅ := by
    rw [erase_eq_empty_iff]; right
    ext x; simp only [mem_univ, mem_singleton, true_iff]; exact Subsingleton.elim x ⊤
  rw [this, sum_empty, sub_zero]

/-- **The second free cumulant is the variance**, `κ₂ = m₂ - m₁²`: the noncrossing partitions of two
points other than `1₂` reduce to the partition into singletons (Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (manuscript numbering), equation (5.3.5) at `n = 2`). -/
theorem freeCumulant_two (m : ℕ → ℂ) : freeCumulant m 2 = m 2 - m 1 ^ 2 := by
  rw [freeCumulant]
  have herase : (univ : Finset (_root_.NoncrossingPartition 2)).erase ⊤ = {discrete 2} := by
    ext P
    simp only [mem_erase, mem_univ, and_true, mem_singleton]
    constructor
    · intro hP
      rcases eq_discrete_or_indiscrete_two P with h | h
      · exact h
      · exact absurd h hP
    · rintro rfl
      exact discrete_two_ne_indiscrete_two
  rw [herase, sum_singleton, discrete_parts, prod_map]
  simp only [Function.Embedding.coeFn_mk, card_singleton, Nat.one_lt_ofNat, dite_true,
    freeCumulant_one, prod_const, card_univ, Fintype.card_fin]

/-- **The R-transform** (Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*
(manuscript numbering),
Definition 5.3.22): the formal power series `R(z) = ∑_{n ≥ 0} κ_{n+1} zⁿ` of the free cumulants
of the moment sequence `m`. -/
noncomputable def rTransform (m : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => freeCumulant m (n + 1)

/-- **Moments of the semicircle law**: the sequence `n ↦ ∫ xⁿ dσ`, as complex numbers. -/
noncomputable def semicircleMoment (n : ℕ) : ℂ :=
  ((∫ x, x ^ n ∂ProbabilityTheory.semicircleReal : ℝ) : ℂ)

/-- **The free cumulants of the semicircle law** (Anderson, Guionnet and Zeitouni, *An Introduction
to Random Matrices*, Example 5.3.26): `κ₂ = 1` and `κₙ = 0` for every other `n ≥ 1`. The moments of
`σ` count noncrossing pair partitions, so the cumulant sequence `[n = 2]` solves the moment-cumulant
formula, and the free cumulants are unique. -/
theorem freeCumulant_semicircle {n : ℕ} (hn : 0 < n) :
    freeCumulant semicircleMoment n = if n = 2 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hm : semicircleMoment n =
        ∑ π : _root_.NoncrossingPartition n, if IsPairPartition π.val then (1 : ℂ) else 0 := by
      rw [semicircleMoment,
        ProbabilityTheory.integral_pow_semicircleReal_eq_card_noncrossing_pairPartition,
        sum_boole, Fintype.card_subtype]
      push_cast; rfl
    have hprod : ∀ π ∈ (univ : Finset (_root_.NoncrossingPartition n)).erase ⊤,
        (∏ V ∈ π.val.parts, if h : V.card < n then freeCumulant semicircleMoment V.card else 0) =
          if IsPairPartition π.val then 1 else 0 := by
      intro π hπ
      have key : ∀ V ∈ π.val.parts, (if h : V.card < n then freeCumulant semicircleMoment V.card
          else 0) = if V.card = 2 then 1 else 0 := by
        intro V hV
        have hlt := card_lt_of_mem_parts_of_ne_top (ne_of_mem_erase hπ) hV
        have hpos : 0 < V.card := card_pos.2 (π.val.nonempty_of_mem_parts hV)
        rw [dite_eq_left hlt, ih _ hlt hpos]
      rw [prod_congr rfl key]
      by_cases hp : IsPairPartition π.val
      · rw [ite_eq_left hp]
        exact prod_eq_one fun V hV => ite_eq_left (hp V hV)
      · rw [ite_eq_right hp]
        obtain ⟨V, hV, hne⟩ : ∃ V ∈ π.val.parts, V.card ≠ 2 := by
          unfold IsPairPartition at hp; push Not at hp; exact hp
        exact prod_eq_zero hV (ite_eq_right hne)
    rw [freeCumulant, sum_congr rfl hprod, hm,
      ← add_sum_erase _ _ (mem_univ (⊤ : _root_.NoncrossingPartition n)), add_sub_cancel_right]
    change (if IsPairPartition (indiscrete n).val then (1 : ℂ) else 0) = _
    by_cases h2 : n = 2
    · subst h2
      rw [ite_eq_left, ite_eq_left rfl]
      intro V hV
      rw [indiscrete_parts_pos (by norm_num), mem_singleton] at hV
      rw [hV, card_univ, Fintype.card_fin]
    · rw [ite_eq_right h2, ite_eq_right]
      intro hpair
      have := hpair univ (by rw [indiscrete_parts_pos hn]; exact mem_singleton_self _)
      rw [card_univ, Fintype.card_fin] at this
      exact h2 this

/-- **The R-transform of the semicircle law is `z`** (Anderson, Guionnet and Zeitouni, *An
Introduction to Random Matrices*, Example 5.3.26): `R_σ(z) = z`, the free analogue of the
cumulant generating function `t²/2` of the standard Gaussian. -/
theorem rTransform_semicircle : rTransform semicircleMoment = PowerSeries.X := by
  ext n
  rw [rTransform, PowerSeries.coeff_mk, freeCumulant_semicircle (Nat.succ_pos n),
    PowerSeries.coeff_X]
  by_cases h : n = 1
  · simp [h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

end MathlibExt.Probability.FreeProbability
