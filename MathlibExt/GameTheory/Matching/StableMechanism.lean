/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.GaleShapley
public import MathlibExt.GameTheory.Matching.StableMatchingLattice
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Stable matching mechanisms and incentives

A *matching mechanism* (Roth's "matching procedure") maps every stated preference profile of a
marriage market to a perfect matching. It is *stable* when it always returns a matching that is
stable for the stated profile, and truthful revelation is a *dominant strategy* for an agent when
no misreport of that agent's preferences, whatever the others state, gives the agent a partner it
truly prefers.

Main result: Roth's impossibility theorem (A. E. Roth, "The economics of matching: stability and
incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, Theorem 3): no stable
matching mechanism makes truthful revelation a dominant strategy for every agent. The proof
follows Roth's: in his market with three men and three women, any stable mechanism lets either
man `m₁` or woman `w₁` gain by misreporting (`roth_stable_mechanism_manipulable`).

The model is that of `MathlibExt.Combinatorics.Matching.GaleShapley` and of Roth (1982), §2:
complete strict preferences and perfect matchings between two sides of equal size. Roth's agents
`m₁, m₂, m₃` and `w₁, w₂, w₃` are `0, 1, 2 : Fin 3` here.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Matching.StableMechanism

open MathlibExt.Combinatorics.Matching.GaleShapley

variable {M W : Type*}

/-! ## Mechanisms and incentives -/

/-- **Matching mechanism.** A rule assigning a perfect matching to every stated profile of men's
and women's strict preferences (Roth, *Math. Oper. Res.* 7 (1982), §4: a "matching procedure"
selecting an outcome for every stated preference profile). -/
abbrev MatchingMechanism (M W : Type*) := MPrefs M W → WPrefs M W → PerfectMatching M W

/-- **Stable matching mechanism.** A mechanism whose outcome is stable for every stated profile
(Roth, *Math. Oper. Res.* 7 (1982), §4, proof of Theorem 3: `h(P) ∈ C(P)` for every `P`). -/
def IsStableMechanism (h : MatchingMechanism M W) : Prop :=
  ∀ mp wp, IsStable mp wp (h mp wp)

/-- **Truthful revelation is dominant for a man.** Whatever preferences the others state, no
report `T` by man `m` gives him a partner he prefers, under his true preference `mp m`, to the
partner he gets by reporting `mp m` (Roth, *Math. Oper. Res.* 7 (1982), §4, the paragraph before
Theorem 3). -/
def IsTruthfulDominantForMan [DecidableEq M] (h : MatchingMechanism M W) (m : M) : Prop :=
  ∀ (mp : MPrefs M W) (wp : WPrefs M W) (T : StrictTotalOrder W),
    ¬ (mp m).lt (h (Function.update mp m T) wp m) (h mp wp m)

/-- **Truthful revelation is dominant for a woman.** Whatever preferences the others state, no
report `T` by woman `w` gives her a partner she prefers, under her true preference `wp w`, to the
partner she gets by reporting `wp w` (Roth, *Math. Oper. Res.* 7 (1982), §4, the paragraph before
Theorem 3). -/
def IsTruthfulDominantForWoman [DecidableEq W] (h : MatchingMechanism M W) (w : W) : Prop :=
  ∀ (mp : MPrefs M W) (wp : WPrefs M W) (T : StrictTotalOrder M),
    ¬ (wp w).lt ((h mp (Function.update wp w T)).symm w) ((h mp wp).symm w)

/-- **Strategy-proof matching mechanism.** Truthful revelation is a dominant strategy for every
man and every woman (Roth, *Math. Oper. Res.* 7 (1982), Theorem 3 and footnote 10). -/
def IsStrategyProof [DecidableEq M] [DecidableEq W] (h : MatchingMechanism M W) : Prop :=
  (∀ m, IsTruthfulDominantForMan h m) ∧ ∀ w, IsTruthfulDominantForWoman h w

/-- **Man-optimal stable matching.** A stable matching that no man likes less than any other
stable matching (Gale and Shapley, *Amer. Math. Monthly* 69 (1962), Theorem 2; Roth, *Math. Oper.
Res.* 7 (1982), Theorem 2). -/
def IsManOptimalStable (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) : Prop :=
  IsStable mp wp μ ∧ ∀ ν, IsStable mp wp ν → ∀ m, ¬ (mp m).lt (ν m) (μ m)

/-- **Every market with sides of equal size has a man-optimal stable matching** (Gale and Shapley,
*Amer. Math. Monthly* 69 (1962), Theorem 2; Roth, *Math. Oper. Res.* 7 (1982), Theorem 2), for
finite sides of equal size; proved through the men's join of stable matchings
(`StableMatchingLattice.exists_stable_forall_not_lt`). -/
theorem exists_isManOptimalStable [Fintype M] [Fintype W]
    (hCard : Fintype.card M = Fintype.card W) (mp : MPrefs M W) (wp : WPrefs M W) :
    ∃ μ, IsManOptimalStable mp wp μ :=
  StableMatchingLattice.exists_stable_forall_not_lt (mp := mp) wp hCard

/-- **Uniqueness of the man-optimal stable matching.** Two man-optimal stable matchings of the
same profile are equal, since preferences are strict (Roth, *Math. Oper. Res.* 7 (1982), §4:
"a unique optimal stable outcome" for each side). -/
theorem IsManOptimalStable.eq {mp : MPrefs M W} {wp : WPrefs M W} {μ ν : PerfectMatching M W}
    (hμ : IsManOptimalStable mp wp μ) (hν : IsManOptimalStable mp wp ν) : μ = ν := by
  ext m
  by_contra h
  rcases (mp m).total h with h' | h'
  · exact hν.2 μ hμ.1 m h'
  · exact hμ.2 ν hν.1 m h'

/-- **Stability without the inverse matching.** A perfect matching is stable iff no man `m` and
woman `w` are such that `m` prefers `w` to his partner and `w` prefers `m` to every man matched
to her (that is, to her partner). -/
theorem isStable_iff_forall_partner (mp : MPrefs M W) (wp : WPrefs M W)
    (μ : PerfectMatching M W) :
    IsStable mp wp μ ↔ ∀ m w, ¬ ((mp m).lt w (μ m) ∧ ∀ m', μ m' = w → (wp w).lt m m') := by
  refine ⟨fun h m w ⟨h₁, h₂⟩ => h m w ⟨h₁, h₂ _ (by simp)⟩, fun h m w ⟨h₁, h₂⟩ => ?_⟩
  refine h m w ⟨h₁, fun m' hm' => ?_⟩
  rwa [show m' = μ.symm w by rw [← hm']; simp]

/-! ## Preferences given by ranks -/

/-- **Preference given by a rank function.** `a` is preferred to `b` when `rk a < rk b`; an
injective rank function gives a strict total order. -/
def rankOrder {α : Type*} (rk : α → ℕ) (hrk : Function.Injective rk) : StrictTotalOrder α where
  lt a b := rk a < rk b
  irrefl _ := lt_irrefl _
  trans h₁ h₂ := lt_trans h₁ h₂
  total h := lt_or_gt_of_ne fun e => h (hrk e)

instance {α : Type*} (rk : α → ℕ) (hrk : Function.Injective rk) :
    DecidableRel (rankOrder rk hrk).lt :=
  fun a b => inferInstanceAs (Decidable (rk a < rk b))

/-- **The ranking `a ≻ b ≻ c` on three agents.** Rank `0` for `a`, `1` for `b`, `2` otherwise. -/
def rank3 (a b : Fin 3) : Fin 3 → ℕ := fun x => if x = a then 0 else if x = b then 1 else 2

/-! ## Roth's market -/

/-- **Men's ranks in Roth's market** (Roth, *Math. Oper. Res.* 7 (1982), proof of Theorem 3):
`m₁ : w₂ ≻ w₁ ≻ w₃`, `m₂ : w₁ ≻ w₂ ≻ w₃`, `m₃ : w₁ ≻ w₂ ≻ w₃`. -/
def rothMenRank : Fin 3 → Fin 3 → ℕ := ![rank3 1 0, rank3 0 1, rank3 0 1]

/-- **Women's ranks in Roth's market** (Roth, *Math. Oper. Res.* 7 (1982), proof of Theorem 3):
`w₁ : m₁ ≻ m₃ ≻ m₂`, `w₂ : m₃ ≻ m₁ ≻ m₂`, `w₃ : m₁ ≻ m₂ ≻ m₃`. -/
def rothWomenRank : Fin 3 → Fin 3 → ℕ := ![rank3 0 2, rank3 2 0, rank3 0 1]

/-- **Man `m₁`'s misreport in Roth's market**, `P''(m₁) : w₂ ≻ w₃ ≻ w₁` (Roth, *Math. Oper. Res.*
7 (1982), proof of Theorem 3). -/
def rothManMisreportRank : Fin 3 → ℕ := rank3 1 2

/-- **Woman `w₁`'s misreport in Roth's market**, `P'(w₁) : m₁ ≻ m₂ ≻ m₃` (Roth, *Math. Oper. Res.*
7 (1982), proof of Theorem 3). -/
def rothWomanMisreportRank : Fin 3 → ℕ := rank3 0 1

/-- **Men's preferences in Roth's market**, from `rothMenRank`. -/
def rothMenPrefs : MPrefs (Fin 3) (Fin 3) :=
  fun m => rankOrder (rothMenRank m) (by revert m; decide)

/-- **Women's preferences in Roth's market**, from `rothWomenRank`. -/
def rothWomenPrefs : WPrefs (Fin 3) (Fin 3) :=
  fun w => rankOrder (rothWomenRank w) (by revert w; decide)

instance (m : Fin 3) : DecidableRel (rothMenPrefs m).lt :=
  fun a b => inferInstanceAs (Decidable (rothMenRank m a < rothMenRank m b))

instance (w : Fin 3) : DecidableRel (rothWomenPrefs w).lt :=
  fun a b => inferInstanceAs (Decidable (rothWomenRank w a < rothWomenRank w b))

/-- **Man `m₁`'s misreported preference** `w₂ ≻ w₃ ≻ w₁` in Roth's market. -/
def rothManMisreport : StrictTotalOrder (Fin 3) := rankOrder rothManMisreportRank (by decide)

/-- **Woman `w₁`'s misreported preference** `m₁ ≻ m₂ ≻ m₃` in Roth's market. -/
def rothWomanMisreport : StrictTotalOrder (Fin 3) := rankOrder rothWomanMisreportRank (by decide)

/-- **The men-preferred stable matching `x` of Roth's market**: `(m₁, w₂), (m₂, w₃), (m₃, w₁)`
(Roth, *Math. Oper. Res.* 7 (1982), proof of Theorem 3). -/
def rothX : PerfectMatching (Fin 3) (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- **The women-preferred stable matching `y` of Roth's market**: `(m₁, w₁), (m₂, w₃), (m₃, w₂)`
(Roth, *Math. Oper. Res.* 7 (1982), proof of Theorem 3). -/
def rothY : PerfectMatching (Fin 3) (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide
  right_inv := by decide

/-- **Stability read off ranks on three agents.** For preferences on `Fin 3` given by rank
functions `r` (men) and `s` (women), the stability condition of `isStable_iff_forall_partner`
stated for a matching function `f`; it is decidable, which the proofs about Roth's market use. -/
def StableByRanks (r s : Fin 3 → Fin 3 → ℕ) (f : Fin 3 → Fin 3) : Prop :=
  ∀ m w, ¬ (r m w < r m (f m) ∧ ∀ m', f m' = w → s w m < s w m')

instance (r s : Fin 3 → Fin 3 → ℕ) (f : Fin 3 → Fin 3) : Decidable (StableByRanks r s f) := by
  unfold StableByRanks; infer_instance

private theorem isStable_iff_byRanks {r s : Fin 3 → Fin 3 → ℕ} {mp : MPrefs (Fin 3) (Fin 3)}
    {wp : WPrefs (Fin 3) (Fin 3)} (hr : ∀ m a b, (mp m).lt a b ↔ r m a < r m b)
    (hs : ∀ w a b, (wp w).lt a b ↔ s w a < s w b) (μ : PerfectMatching (Fin 3) (Fin 3)) :
    IsStable mp wp μ ↔ StableByRanks r s μ := by
  rw [isStable_iff_forall_partner]
  simp only [StableByRanks, hr, hs]

private theorem stable_iff_of_byRanks {r s : Fin 3 → Fin 3 → ℕ} {mp : MPrefs (Fin 3) (Fin 3)}
    {wp : WPrefs (Fin 3) (Fin 3)} (hr : ∀ m a b, (mp m).lt a b ↔ r m a < r m b)
    (hs : ∀ w a b, (wp w).lt a b ↔ s w a < s w b) {p : (Fin 3 → Fin 3) → Prop}
    (key : ∀ f : Fin 3 → Fin 3, Function.Injective f → (StableByRanks r s f ↔ p f))
    (μ : PerfectMatching (Fin 3) (Fin 3)) : IsStable mp wp μ ↔ p μ := by
  rw [isStable_iff_byRanks hr hs]
  exact key μ μ.injective

/-- **Roth's market has exactly the two stable matchings `x` and `y`** (Roth, *Math. Oper. Res.*
7 (1982), proof of Theorem 3: `C(P) = {x, y}`). -/
theorem roth_isStable_iff (μ : PerfectMatching (Fin 3) (Fin 3)) :
    IsStable rothMenPrefs rothWomenPrefs μ ↔ μ = rothX ∨ μ = rothY := by
  rw [stable_iff_of_byRanks (r := rothMenRank) (s := rothWomenRank) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => Iff.rfl) (p := fun f => (∀ i, f i = rothX i) ∨ ∀ i, f i = rothY i)
    (by decide)]
  simp only [← Equiv.ext_iff]

/-- The men's ranks after `m₁`'s misreport. -/
private def rothMenRank'' : Fin 3 → Fin 3 → ℕ := ![rothManMisreportRank, rank3 0 1, rank3 0 1]

/-- The women's ranks after `w₁`'s misreport. -/
private def rothWomenRank' : Fin 3 → Fin 3 → ℕ := ![rothWomanMisreportRank, rank3 2 0, rank3 0 1]

/-- **After `m₁`'s misreport, `x` is the unique stable matching** (Roth, *Math. Oper. Res.* 7
(1982), proof of Theorem 3: `C(P'') = {x}`). -/
theorem roth_isStable_manMisreport_iff (μ : PerfectMatching (Fin 3) (Fin 3)) :
    IsStable (Function.update rothMenPrefs 0 rothManMisreport) rothWomenPrefs μ ↔ μ = rothX := by
  rw [stable_iff_of_byRanks (r := rothMenRank'') (s := rothWomenRank)
    (fun m _ _ => by fin_cases m <;> exact Iff.rfl) (fun _ _ _ => Iff.rfl)
    (p := fun f => ∀ i, f i = rothX i) (by decide)]
  simp only [← Equiv.ext_iff]

/-- **After `w₁`'s misreport, `y` is the unique stable matching** (Roth, *Math. Oper. Res.* 7
(1982), proof of Theorem 3: `C(P') = {y}`). -/
theorem roth_isStable_womanMisreport_iff (μ : PerfectMatching (Fin 3) (Fin 3)) :
    IsStable rothMenPrefs (Function.update rothWomenPrefs 0 rothWomanMisreport) μ ↔
      μ = rothY := by
  rw [stable_iff_of_byRanks (r := rothMenRank) (s := rothWomenRank')
    (fun _ _ _ => Iff.rfl) (fun w _ _ => by fin_cases w <;> exact Iff.rfl)
    (p := fun f => ∀ i, f i = rothY i) (by decide)]
  simp only [← Equiv.ext_iff]

/-- **In Roth's market every stable mechanism is manipulable** (Roth, *Math. Oper. Res.* 7
(1982), proof of Theorem 3): for every stable matching mechanism `h`, at Roth's profile either
man `m₁` gains by reporting `w₂ ≻ w₃ ≻ w₁`, or woman `w₁` gains by reporting `m₁ ≻ m₂ ≻ m₃`. -/
theorem roth_stable_mechanism_manipulable (h : MatchingMechanism (Fin 3) (Fin 3))
    (hh : IsStableMechanism h) :
    (rothMenPrefs 0).lt (h (Function.update rothMenPrefs 0 rothManMisreport) rothWomenPrefs 0)
        (h rothMenPrefs rothWomenPrefs 0) ∨
      (rothWomenPrefs 0).lt
        ((h rothMenPrefs (Function.update rothWomenPrefs 0 rothWomanMisreport)).symm 0)
        ((h rothMenPrefs rothWomenPrefs).symm 0) := by
  have hx := (roth_isStable_manMisreport_iff _).1 (hh _ _)
  have hy := (roth_isStable_womanMisreport_iff _).1 (hh _ _)
  rw [hx, hy]
  set μ := h rothMenPrefs rothWomenPrefs
  by_cases h0 : μ 0 = 0
  · left
    rw [h0]
    change rothMenRank 0 (rothX 0) < rothMenRank 0 0
    decide
  · right
    have hs : μ.symm 0 ≠ 0 := fun e => h0 (μ.symm_apply_eq.mp e).symm
    change rothWomenRank 0 (rothY.symm 0) < rothWomenRank 0 (μ.symm 0)
    generalize μ.symm 0 = k at hs
    revert k
    decide

/-- **Roth's impossibility theorem** (Roth, *Math. Oper. Res.* 7 (1982), Theorem 3): no stable
matching mechanism makes truthful revelation a dominant strategy for all agents. As in the source,
it is proved for one market, with three men and three women. -/
theorem not_exists_stable_strategyProof :
    ¬ ∃ h : MatchingMechanism (Fin 3) (Fin 3), IsStableMechanism h ∧ IsStrategyProof h := by
  rintro ⟨h, hh, hm, hw⟩
  rcases roth_stable_mechanism_manipulable h hh with e | e
  · exact hm 0 _ _ _ e
  · exact hw 0 _ _ _ e

end MathlibExt.GameTheory.Matching.StableMechanism
