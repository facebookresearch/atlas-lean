/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.GaleShapley
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! # The rural hospitals theorem for marriage markets

A marriage market in which agents may remain single: each man ranks the women and the option of
remaining single (`none : Option W`) by a strict total order, and each woman ranks the men and
`none : Option M` in the same way. A matching is a partial bijection `μ : M ≃. W` (Mathlib's
`PEquiv`): `μ m` is the partner of man `m` and `μ.symm w` that of woman `w`, `none` meaning
single. It is stable when it is individually rational (nobody prefers being single to the
assigned partner) and no man and woman prefer each other to their assignments.

Relation to the stable marriage model of `MathlibExt.Combinatorics.Matching.GaleShapley`
(perfect matchings `M ≃ W`, complete lists): a perfect matching `μ` is the partial bijection
`μ.toPEquiv`, and when every partner is preferred to remaining single (`withSingleLast`),
stability in the two models agrees (`isStableSingle_toPEquiv_iff`).

Main result: in a finite market, every stable matching matches the same set of men and the same
set of women. This is the marriage case (every quota equal to one) of Roth, "On the allocation of
residents to rural hospitals: a general property of two-sided matching markets", *Econometrica*
54 (1986), 425–427, Lemma 1 (which Roth credits to his 1984 *J. Polit. Econ.* paper and to Gale
and Sotomayor 1985) and of the Theorem of that note: a woman who is single at one stable matching
is single at every stable matching. Here the women play Roth's hospitals and the men his
students. The proof is a counting argument comparing the agents who prefer one stable matching
to the other, not Roth's.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Matching.RuralHospitals

open MathlibExt.Order
open MathlibExt.Combinatorics.Matching.GaleShapley (MPrefs WPrefs PerfectMatching IsStable
  gale_shapley_exists_stable_matching_general)

variable {M W : Type*}

/-- **Men's preferences with the option of remaining single.** Each man has a strict total
order on `Option W`, where `none` is remaining single and `a` before `b` means that `a` is
preferred (Roth, *Econometrica* 54 (1986), p. 425: a strict preference ordering over the set
`H ∪ {u}`, with `u` the possibility of remaining unmatched). -/
abbrev MPrefsSingle (M W : Type*) := M → StrictTotalOrder (Option W)

/-- **Women's preferences with the option of remaining single.** Each woman has a strict total
order on `Option M`, where `none` is remaining single (Roth, *Econometrica* 54 (1986), p. 426). -/
abbrev WPrefsSingle (M W : Type*) := W → StrictTotalOrder (Option M)

/-- **Stable matching with singles** (Roth, *Econometrica* 54 (1986), p. 426, with every quota
equal to one). A partial bijection `μ : M ≃. W` is stable when no agent prefers being single to
the assigned partner (individual rationality), and no man `m` and woman `w` each prefer the
other to the assigned partner. -/
def IsStableSingle (mp : MPrefsSingle M W) (wp : WPrefsSingle M W) (μ : M ≃. W) : Prop :=
  (∀ m, ¬ (mp m).lt none (μ m)) ∧ (∀ w, ¬ (wp w).lt none (μ.symm w)) ∧
    ∀ m w, ¬ ((mp m).lt (some w) (μ m) ∧ (wp w).lt (some m) (μ.symm w))

/-- **Stability does not depend on which side is called the men.** A partial bijection is stable
iff its inverse is stable for the market with the two sides exchanged. -/
theorem isStableSingle_symm_iff (mp : MPrefsSingle M W) (wp : WPrefsSingle M W) (μ : M ≃. W) :
    IsStableSingle wp mp μ.symm ↔ IsStableSingle mp wp μ := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, fun m w h => h₃ w m h.symm⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, fun w m h => h₃ m w h.symm⟩⟩

/-! ## Complete preference lists -/

/-- **Remaining single ranked last.** The strict order on `Option α` that extends `T` and ranks
`none` (remaining single) below every element: every partner is acceptable. -/
def withSingleLast {α : Type*} (T : StrictTotalOrder α) : StrictTotalOrder (Option α) where
  lt
    | some a, some b => T.lt a b
    | some _, none => True
    | none, _ => False
  irrefl
    | some a => T.irrefl a
    | none => id
  trans {a b c} h₁ h₂ := by
    match a, b, c, h₁, h₂ with
    | some _, some _, some _, h₁, h₂ => exact T.trans h₁ h₂
    | some _, some _, none, _, _ => trivial
    | some _, none, none, _, h₂ => exact h₂.elim
    | some _, none, some _, _, h₂ => exact h₂.elim
    | none, _, _, h₁, _ => exact h₁.elim
  total {a b} h := by
    match a, b with
    | some a, some b => exact T.total fun e => h (congrArg some e)
    | some _, none => exact Or.inl trivial
    | none, some _ => exact Or.inr trivial
    | none, none => exact absurd rfl h

/-- **Bridge to the stable marriage model.** With complete lists (remaining single ranked last),
a perfect matching `μ : M ≃ W` is stable as a matching with singles (`μ.toPEquiv`) iff it is
stable in the sense of `GaleShapley.IsStable`. -/
theorem isStableSingle_toPEquiv_iff (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) :
    IsStableSingle (fun m => withSingleLast (mp m)) (fun w => withSingleLast (wp w))
      μ.toPEquiv ↔ IsStable mp wp μ := by
  simp only [IsStableSingle, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply]
  exact ⟨fun ⟨_, _, h⟩ m w hb => h m w hb,
    fun h => ⟨fun _ => id, fun _ => id, fun m w hb => h m w hb⟩⟩

variable {mp : MPrefsSingle M W} {wp : WPrefsSingle M W} {μ ν : M ≃. W}

/-- A man who prefers `μ` to `ν` is matched in `μ` to a woman who prefers `ν` to `μ`. -/
private theorem woman_of_man_prefers (hν : IsStableSingle mp wp ν) {m : M}
    (hm : (mp m).lt (μ m) (ν m)) :
    ∃ w, μ m = some w ∧ (wp w).lt (ν.symm w) (μ.symm w) := by
  rcases hμm : μ m with _ | w
  · rw [hμm] at hm; exact absurd hm (hν.1 m)
  · refine ⟨w, rfl, ?_⟩
    rw [hμm] at hm
    have hμw : μ.symm w = some m := μ.eq_some_iff.2 hμm
    have hne : ν.symm w ≠ some m := fun e => by
      rw [ν.eq_some_iff.1 e] at hm; exact (mp m).irrefl _ hm
    rw [hμw]
    exact ((wp w).total hne).resolve_right fun h => hν.2.2 m w ⟨hm, h⟩

/-- A woman who prefers `ν` to `μ` is matched in `ν` to a man who prefers `μ` to `ν`. -/
private theorem man_of_woman_prefers (hμ : IsStableSingle mp wp μ) {w : W}
    (hw : (wp w).lt (ν.symm w) (μ.symm w)) :
    ∃ m, ν.symm w = some m ∧ (mp m).lt (μ m) (ν m) := by
  rcases hνw : ν.symm w with _ | m
  · rw [hνw] at hw; exact absurd hw (hμ.2.1 w)
  · refine ⟨m, rfl, ?_⟩
    rw [hνw] at hw
    have hνm : ν m = some w := ν.eq_some_iff.1 hνw
    have hne : μ m ≠ some w := fun e => by
      rw [μ.eq_some_iff.2 e] at hw; exact (wp w).irrefl _ hw
    rw [hνm]
    exact ((mp m).total hne).resolve_right fun h => hμ.2.2 m w ⟨h, hw⟩

/-- **A man matched at one stable matching is matched at every stable matching** (Roth,
*Econometrica* 54 (1986), Lemma 1, marriage case). -/
theorem isSome_of_isStableSingle [Finite M] [Finite W] (hμ : IsStableSingle mp wp μ)
    (hν : IsStableSingle mp wp ν) {m : M} (h : (μ m).isSome) : (ν m).isSome := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite W
  by_contra hn
  rw [Option.not_isSome_iff_eq_none] at hn
  obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 h
  -- `m` prefers his partner in `μ` to being single in `ν`.
  have hmA : (mp m).lt (μ m) (ν m) := by
    rw [hn, hw₀]
    have hne : (some w₀ : Option W) ≠ none := Option.some_ne_none w₀
    exact ((mp m).total hne).resolve_right (by rw [← hw₀]; exact hμ.1 m)
  set A := Finset.univ.filter fun m => (mp m).lt (μ m) (ν m)
  set B := Finset.univ.filter fun w => (wp w).lt (ν.symm w) (μ.symm w)
  have hAB : A.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun m => (μ m).getD w₀) (fun a ha => ?_) ?_
    · obtain ⟨w, hw, hwB⟩ := woman_of_man_prefers hν (Finset.mem_filter.1 ha).2
      simpa [B, hw] using hwB
    · intro a ha b hb hab
      obtain ⟨w, hw, -⟩ := woman_of_man_prefers hν (Finset.mem_filter.1 ha).2
      obtain ⟨w', hw', -⟩ := woman_of_man_prefers hν (Finset.mem_filter.1 hb).2
      simp only [hw, hw', Option.getD_some] at hab
      subst hab
      exact Option.some_injective _ ((μ.eq_some_iff.2 hw).symm.trans (μ.eq_some_iff.2 hw'))
  have hBA : B.card ≤ (A.erase m).card := by
    refine Finset.card_le_card_of_injOn (fun w => (ν.symm w).getD m) (fun a ha => ?_) ?_
    · obtain ⟨m', hm', hm'A⟩ := man_of_woman_prefers hμ (Finset.mem_filter.1 ha).2
      have hne : m' ≠ m := fun e => by
        rw [e] at hm'; rw [ν.eq_some_iff.1 hm'] at hn; exact Option.some_ne_none _ hn
      simpa [A, hm', hne] using hm'A
    · intro a ha b hb hab
      obtain ⟨m', hm', -⟩ := man_of_woman_prefers hμ (Finset.mem_filter.1 ha).2
      obtain ⟨m'', hm'', -⟩ := man_of_woman_prefers hμ (Finset.mem_filter.1 hb).2
      simp only [hm', hm'', Option.getD_some] at hab
      subst hab
      exact Option.some_injective _ ((ν.eq_some_iff.1 hm').symm.trans (ν.eq_some_iff.1 hm''))
  have hmem : m ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmA⟩
  have := Finset.card_erase_lt_of_mem hmem
  omega

/-- **Rural hospitals theorem, marriage case: every stable matching matches the same men**
(Roth, *Econometrica* 54 (1986), Lemma 1 with all quotas equal to one). In a finite market with
singles, a man has a partner at one stable matching iff he has one at every stable matching. -/
theorem isSome_iff_of_isStableSingle [Finite M] [Finite W] (hμ : IsStableSingle mp wp μ)
    (hν : IsStableSingle mp wp ν) (m : M) : (μ m).isSome ↔ (ν m).isSome :=
  ⟨isSome_of_isStableSingle hμ hν, isSome_of_isStableSingle hν hμ⟩

/-- **Rural hospitals theorem, marriage case: every stable matching matches the same women**
(Roth, *Econometrica* 54 (1986), Theorem and Lemma 1, with all quotas equal to one). In a finite
market with singles, a woman has a partner at one stable matching iff she has one at every
stable matching; with the women as Roth's hospitals, a woman single at one stable matching is
single at every stable matching. -/
theorem isSome_symm_iff_of_isStableSingle [Finite M] [Finite W] (hμ : IsStableSingle mp wp μ)
    (hν : IsStableSingle mp wp ν) (w : W) : (μ.symm w).isSome ↔ (ν.symm w).isSome :=
  isSome_iff_of_isStableSingle ((isStableSingle_symm_iff mp wp μ).2 hμ)
    ((isStableSingle_symm_iff mp wp ν).2 hν) w

/-- **With complete lists every stable matching is perfect.** If the two sides are finite of the
same size and every partner is preferred to remaining single, every stable matching with singles
matches every man: the Gale–Shapley theorem gives a stable perfect matching, which is stable with
singles by `isStableSingle_toPEquiv_iff`, and the rural hospitals theorem transfers its matched
men to every stable matching. So the rural hospitals theorem says nothing new in the perfect
matching model. -/
theorem isSome_of_isStableSingle_withSingleLast [Fintype M] [Fintype W]
    (hCard : Fintype.card M = Fintype.card W) (mp : MPrefs M W) (wp : WPrefs M W)
    {μ : M ≃. W}
    (hμ : IsStableSingle (fun m => withSingleLast (mp m)) (fun w => withSingleLast (wp w)) μ)
    (m : M) : (μ m).isSome := by
  obtain ⟨ν, hν⟩ := gale_shapley_exists_stable_matching_general hCard mp wp
  refine (isSome_iff_of_isStableSingle ((isStableSingle_toPEquiv_iff mp wp ν).2 hν) hμ m).1 ?_
  simp [Equiv.toPEquiv_apply]

end MathlibExt.GameTheory.Matching.RuralHospitals
