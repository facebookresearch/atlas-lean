/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.PatternContainment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FinCases

/-!
# Permutations avoiding 231 and 3124

`card_avoid_231_3124_pos_zero` counts the avoiders with zero at a prescribed nonfinal
position by identifying the interval of values occupied by their suffix.
For `n ≥ 1`, `card_avoid_231_3124` sums over the position of zero, including the
unique decreasing permutation with zero last, to obtain the count `F_{2n-1}`.

## References

* Juan B. Gil, Felix H. Xu, and William Y. Zhu, *Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
  Permutations*, INTEGERS 25 (2025), Article A79, pp. 1–19, Propositions 10 and 11.
  The proof of Proposition 10 here uses the position count of Proposition 11 instead of the
  paper's first-entry case split. The finite checks for occurrences of `321` and `4123`
  follow the checks for `231` and `3124` in this module
  (`card_avoid_231_3124_pos_zero.has231_iff` and `card_avoid_231_3124_pos_zero.has3124_iff`).
* Earlier work on the nine symmetry classes, cited in Section 1 of the above article:
  M. D. Atkinson, *Restricted permutations*, Discrete Mathematics 195 (1999), no. 1–3,
  pp. 27–38; and Julian West, *Generating trees and forbidden subsequences*, Discrete
  Mathematics 157 (1996), no. 1–3, pp. 363–374.
-/

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

@[expose] public section

/-- **The pattern $321$.** The pattern $321$ written with values $0, 1, 2$: the map from
$\{0, 1, 2\}$ to itself sending $0 \mapsto 2$, $1 \mapsto 1$ and $2 \mapsto 0$. -/
def pat321 : Fin 3 → Fin 3 := ![2, 1, 0]

/-- **The pattern $231$.** The pattern $231$ written with values $0, 1, 2$: the map from
$\{0, 1, 2\}$ to itself sending $0 \mapsto 1$, $1 \mapsto 2$ and $2 \mapsto 0$. -/
def pat231 : Fin 3 → Fin 3 := ![1, 2, 0]

/-- **The permutation pattern $4123$.** The pattern $4123$ with its values shifted down by
one: the map $\{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ sending $0, 1, 2, 3$ to $3, 0, 1, 2$
respectively. -/
def pat4123 : Fin 4 → Fin 4 := ![3, 0, 1, 2]

/-- **The permutation pattern $3412$.** The pattern $3412$ with its values shifted down by
one: the map $\{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ sending $0, 1, 2, 3$ to $2, 3, 0, 1$
respectively. -/
def pat3412 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- **The pattern $3124$.** The pattern $3124$ written with values $0, 1, 2, 3$: the map from
$\{0, 1, 2, 3\}$ to itself sending $0 \mapsto 2$, $1 \mapsto 0$, $2 \mapsto 1$ and $3 \mapsto 3$. -/
def pat3124 : Fin 4 → Fin 4 := ![2, 0, 1, 3]

/-- **Occurrences of $321$.** This pattern occurs exactly when three increasing positions
have strictly decreasing values. -/
theorem hasPattern_pat321_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HasPattern σ pat321 ↔ ∃ a b c, a < b ∧ b < c ∧ σ c < σ b ∧ σ b < σ a := by
  rw [hasPattern_iff_exists_orderEmbedding]
  constructor
  · rintro ⟨e, h⟩
    exact ⟨e 0, e 1, e 2, e.strictMono (by decide), e.strictMono (by decide),
      (h 2 1).2 (by decide), (h 1 0).2 (by decide)⟩
  · rintro ⟨a, b, c, hab, hbc, hcb, hba⟩
    have he : StrictMono (![a, b, c] : Fin 3 → Fin n) :=
      Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> assumption)
    refine ⟨OrderEmbedding.ofStrictMono _ he, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pat321] <;> omega

/-- **Occurrences of $4123$.** This pattern occurs exactly when four increasing positions
have values whose last three are increasing and all below the first. -/
theorem hasPattern_pat4123_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HasPattern σ pat4123 ↔
      ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ σ b < σ c ∧ σ c < σ d ∧ σ d < σ a := by
  rw [hasPattern_iff_exists_orderEmbedding]
  constructor
  · rintro ⟨e, h⟩
    exact ⟨e 0, e 1, e 2, e 3, e.strictMono (by decide), e.strictMono (by decide),
      e.strictMono (by decide), (h 1 2).2 (by decide), (h 2 3).2 (by decide), (h 3 0).2 (by decide)⟩
  · rintro ⟨a, b, c, d, hab, hbc, hcd, hbc', hcd', hda⟩
    have he : StrictMono (![a, b, c, d] : Fin 4 → Fin n) :=
      Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> assumption)
    refine ⟨OrderEmbedding.ofStrictMono _ he, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pat4123] <;> omega

end

namespace card_avoid_231_3124_pos_zero

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

private theorem has231_iff {n : ℕ} (σ : Perm n) :
    HasPattern σ pat231 ↔
      ∃ a b c, a < b ∧ b < c ∧ σ c < σ a ∧ σ a < σ b := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e 0, e 1, e 2, he 0 1 (by decide), he 1 2 (by decide),
      (h 2 0).2 (by decide), (h 0 1).2 (by decide)⟩
  · rintro ⟨a, b, c, hab, hbc, hca, hab'⟩
    have he : StrictMono (![a, b, c] : Fin 3 → Fin n) :=
      Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> assumption)
    refine ⟨_, fun _ _ h => he h, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pat231] <;> omega

private theorem has3124_iff {n : ℕ} (σ : Perm n) :
    HasPattern σ pat3124 ↔
      ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ σ b < σ c ∧ σ c < σ a ∧ σ a < σ d := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e 0, e 1, e 2, e 3, he 0 1 (by decide), he 1 2 (by decide),
      he 2 3 (by decide), (h 1 2).2 (by decide), (h 2 0).2 (by decide),
      (h 0 3).2 (by decide)⟩
  · rintro ⟨a, b, c, d, hab, hbc, hcd, hbc', hca, had⟩
    have he : StrictMono (![a, b, c, d] : Fin 4 → Fin n) :=
      Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i <;> assumption)
    refine ⟨_, fun _ _ h => he h, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pat3124] <;> omega

private abbrev Avoids {n : ℕ} (σ : Perm n) := ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124

-- Leave a gap of length s immediately above t in the ordered prefix values.
private def skip {p : ℕ} (s : ℕ) (t x : Fin p) : Fin (p + s) :=
  ⟨if x ≤ t then x.val else x.val + s, by split <;> omega⟩

private theorem skip_mono {p s : ℕ} (t : Fin p) : StrictMono (skip s t) := by
  intro x y h
  simp only [skip, Fin.lt_def, Fin.le_def] at *
  split_ifs <;> omega

private def shift {p s : ℕ} (t : Fin p) (x : Fin s) : Fin (p + s) :=
  ⟨t.val + 1 + x.val, by omega⟩

private theorem shift_lt {p s : ℕ} (t : Fin p) (x y : Fin s) :
    shift t x < shift t y ↔ x < y := by
  change t.val + 1 + x.val < t.val + 1 + y.val ↔ x.val < y.val
  omega

private theorem separated {p s : ℕ} (t x : Fin p) (y z : Fin s) :
    ¬ (shift t y < skip s t x ∧ skip s t x < shift t z) := by
  simp only [shift, skip, Fin.lt_def, Fin.le_def]
  split_ifs <;> omega

private noncomputable def assemble {p s : ℕ} (t : Fin p) (τ : Perm s) : Perm (p + s) := by
  let f := Fin.addCases (motive := fun _ => Fin (p + s))
    (fun i => skip s t i.rev) (fun i => shift t (τ i))
  refine Equiv.ofBijective f (Function.Injective.bijective_of_finite ?_)
  have disjoint (i : Fin p) (j : Fin s) : skip s t i ≠ shift t j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [skip, shift, Fin.le_def] at hv
    split_ifs at hv <;> omega
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp only
    [f, Fin.addCases_left, Fin.addCases_right]
  · intro h
    exact congrArg _ (Fin.rev_injective ((skip_mono t).injective h))
  · exact fun h => (disjoint _ _ h).elim
  · exact fun h => (disjoint _ _ h.symm).elim
  · intro h
    apply congrArg _ (τ.injective _)
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

@[simp] private theorem assemble_left {p s : ℕ} (t i : Fin p) (τ : Perm s) :
    assemble t τ (i.castAdd s) = skip s t i.rev := by simp [assemble]

@[simp] private theorem assemble_right {p s : ℕ} (t : Fin p) (τ : Perm s) (i : Fin s) :
    assemble t τ (i.natAdd p) = shift t (τ i) := by simp [assemble]

private theorem suffix_lift {p s : ℕ} {i : Fin (p + s)} (hi : p ≤ i.val) :
    ∃ x : Fin s, x.natAdd p = i :=
  ⟨⟨i.val - p, by omega⟩, Fin.ext (by change p + (i.val - p) = i.val; omega)⟩

private theorem prefix_descent {p s : ℕ} (t : Fin p) (τ : Perm s) {a b : Fin (p + s)}
    (hab : a < b) (hb : b.val < p) : assemble t τ b < assemble t τ a := by
  have ha : a.val < p := by omega
  change assemble t τ ((b.castLT hb).castAdd s) < assemble t τ ((a.castLT ha).castAdd s)
  simp only [assemble_left]
  exact skip_mono t (Fin.rev_lt_rev.mpr hab)

private theorem prefix_separated {p s : ℕ} (t : Fin p) (τ : Perm s) {a b c : Fin (p + s)}
    (ha : a.val < p) (hb : p ≤ b.val) (hc : p ≤ c.val) :
    ¬ (assemble t τ b < assemble t τ a ∧ assemble t τ a < assemble t τ c) := by
  obtain ⟨i, rfl⟩ := suffix_lift hb
  obtain ⟨j, rfl⟩ := suffix_lift hc
  change ¬ (_ < assemble t τ ((a.castLT ha).castAdd s) ∧
    assemble t τ ((a.castLT ha).castAdd s) < _)
  simpa only [assemble_left, assemble_right] using separated t (a.castLT ha).rev (τ i) (τ j)

private theorem lift_pattern {p s k : ℕ} (t : Fin p) (τ : Perm s) (π : Fin k → Fin k) :
    HasPattern τ π → HasPattern (assemble t τ) π := by
  rintro ⟨e, he, hv⟩
  refine ⟨fun i => (e i).natAdd p, fun i j hij => by simpa using he i j hij, ?_⟩
  intro i j
  simpa only [assemble_right, shift_lt] using hv i j

private theorem restrict_pattern {p s k : ℕ} {t : Fin p} {τ : Perm s}
    {π : Fin (k + 1) → Fin (k + 1)} (e : Fin (k + 1) → Fin (p + s))
    (he : StrictMono e) (hv : ∀ i j, assemble t τ (e i) < assemble t τ (e j) ↔ π i < π j)
    (h : p ≤ (e 0).val) : HasPattern τ π := by
  have hpos (i) : p ≤ (e i).val := h.trans (he.monotone (Fin.zero_le i))
  choose f hf using fun i => suffix_lift (hpos i)
  refine ⟨f, fun i j hij => ?_, fun i j => ?_⟩
  · have hij' := he hij
    rw [← hf i, ← hf j] at hij'
    simpa using hij'
  · simpa only [← hf i, ← hf j, assemble_right, shift_lt] using hv i j

private theorem avoids_assemble {p s : ℕ} (t : Fin p) (τ : Perm s) (hτ : Avoids τ) :
    Avoids (assemble t τ) := by
  constructor
  · rintro ⟨e, he, hv⟩
    apply hτ.1 (restrict_pattern e (fun {_ _} h => he _ _ h) hv ?_)
    by_contra! ha
    have hab := (hv 0 1).2 (by decide)
    have hca := (hv 2 0).2 (by decide)
    by_cases hb : (e 1).val < p
    · exact hab.asymm (prefix_descent t τ (he 0 1 (by decide)) hb)
    · have hbc := he 1 2 (by decide)
      exact prefix_separated t τ ha (by omega : p ≤ (e 2).val) (by omega) ⟨hca, hab⟩
  · rintro ⟨e, he, hv⟩
    apply hτ.2 (restrict_pattern e (fun {_ _} h => he _ _ h) hv ?_)
    by_contra! ha
    have hbc := (hv 1 2).2 (by decide)
    have hca := (hv 2 0).2 (by decide)
    have had := (hv 0 3).2 (by decide)
    by_cases hc : (e 2).val < p
    · exact hbc.asymm (prefix_descent t τ (he 1 2 (by decide)) hc)
    · have hcd := he 2 3 (by decide)
      exact prefix_separated t τ ha (by omega) (by omega) ⟨hca, had⟩

private abbrev pivot (m s : ℕ) := (Fin.last m).castAdd s

-- An ascent before zero would complete a 231 occurrence with zero.
private theorem descending {m s : ℕ} {σ : Perm (m + 1 + s)} (hσ : Avoids σ)
    (hz : (σ (pivot m s)).val = 0) {a b : Fin (m + 1 + s)}
    (hab : a < b) (hb : b.val ≤ m) : σ b < σ a := by
  have ha : a < pivot m s := by change a.val < m; omega
  have hpos : 0 < (σ a).val := by
    have := σ.injective.ne ha.ne
    simp only [ne_eq, Fin.ext_iff] at this
    omega
  by_contra! h
  have hlt := lt_of_le_of_ne h (σ.injective.ne hab.ne)
  have hb' : b < pivot m s := by
    apply lt_of_le_of_ne (show b ≤ pivot m s from hb)
    rintro rfl
    omega
  exact hσ.1 ((has231_iff σ).2 ⟨a, b, _, hab, hb', by omega, hlt⟩)

-- If suffix values straddled a prefix value, their order would give either 231 or 3124.
private theorem no_straddle {m s : ℕ} {σ : Perm (m + 1 + s)} (hσ : Avoids σ)
    (hz : (σ (pivot m s)).val = 0) {a : Fin (m + 1 + s)} (ha : a.val ≤ m) (i j : Fin s) :
    ¬ (σ (i.natAdd (m + 1)) < σ a ∧ σ a < σ (j.natAdd (m + 1))) := by
  rintro ⟨hi, hj⟩
  have hpi : pivot m s < i.natAdd (m + 1) := by
    change m < m + 1 + _
    omega
  have hpj : pivot m s < j.natAdd (m + 1) := by
    change m < m + 1 + _
    omega
  have hap : a < pivot m s := by
    apply lt_of_le_of_ne (show a ≤ pivot m s from ha)
    rintro rfl
    omega
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hz' : σ (pivot m s) < σ (i.natAdd (m + 1)) := by
      have := σ.injective.ne hpi.ne
      simp only [ne_eq, Fin.ext_iff] at this
      omega
    exact hσ.2 ((has3124_iff σ).2 ⟨a, _, _, _, hap, hpi, by simpa using hij, hz', hi, hj⟩)
  · exact hi.asymm hj
  · exact hσ.1 ((has231_iff σ).2 ⟨a, _, _, hap.trans hpj, by simpa using hji, hi, hj⟩)

private theorem prefix_range {p s : ℕ} (σ : Perm (p + s)) :
    Set.range (fun i : Fin p => σ (i.rev.castAdd s)) =
      (Set.range fun j : Fin s => σ (j.natAdd p))ᶜ := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val (σ.injective hj)
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  · intro hy
    obtain ⟨x, rfl⟩ := σ.surjective y
    induction x using Fin.addCases with
    | left i => exact ⟨i.rev, by simp⟩
    | right j => exact (hy ⟨j, rfl⟩).elim

-- Two permutations decreasing on the prefix are determined by their common suffix.
private theorem eq_of_suffix {p s : ℕ} {σ ρ : Perm (p + s)}
    (hσ : StrictMono fun i : Fin p => σ (i.rev.castAdd s))
    (hρ : StrictMono fun i : Fin p => ρ (i.rev.castAdd s))
    (h : ∀ i : Fin s, σ (i.natAdd p) = ρ (i.natAdd p)) : σ = ρ := by
  have he := hσ.range_inj_of_wellFoundedLT hρ |>.mp (by rw [prefix_range, prefix_range, funext h])
  apply Equiv.ext
  intro x
  induction x using Fin.addCases with
  | left i => simpa using congrFun he i.rev
  | right j => exact h j

-- The suffix has s distinct values and contains every value between its two extremes.
private theorem suffix_interval {m s : ℕ} (hs : 0 < s) {σ : Perm (m + 1 + s)}
    (hσ : Avoids σ) (hz : (σ (pivot m s)).val = 0) :
    ∃ t : Fin (m + 1), ∀ i : Fin s, t.val < (σ (i.natAdd (m + 1))).val ∧
      (σ (i.natAdd (m + 1))).val ≤ t.val + s := by
  let f (i : Fin s) := σ (i.natAdd (m + 1))
  let S := Finset.univ.image f
  have hf : Function.Injective f := σ.injective.comp (Fin.natAdd_injective s _)
  have mem (i : Fin s) : f i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hS : S.Nonempty := ⟨_, mem ⟨0, hs⟩⟩
  let lo := S.min' hS
  let hi := S.max' hS
  have hlo : lo ∈ S := S.min'_mem hS
  have hhi : hi ∈ S := S.max'_mem hS
  obtain ⟨i, _, hiMin⟩ := Finset.mem_image.mp hlo
  obtain ⟨j, _, hjMax⟩ := Finset.mem_image.mp hhi
  have hpos : 0 < lo.val := by
    have hne : i.natAdd (m + 1) ≠ pivot m s := by
      intro he
      have := congrArg Fin.val he
      simp only [pivot, Fin.val_natAdd, Fin.val_castAdd, Fin.val_last] at this
      omega
    have hne' := σ.injective.ne hne
    change f i ≠ _ at hne'
    rw [hiMin] at hne'
    simp only [ne_eq, Fin.ext_iff] at hne'
    omega
  have heq : S = Finset.Icc lo hi := by
    ext x
    rw [Finset.mem_Icc]
    constructor
    · intro hx
      exact ⟨S.min'_le _ hx, S.le_max' _ hx⟩
    · rintro ⟨hl, hu⟩
      by_contra hx
      have hl' := lt_of_le_of_ne hl (fun e => hx (e ▸ hlo))
      have hu' := lt_of_le_of_ne hu (fun e => hx (e ▸ hhi))
      obtain ⟨a, rfl⟩ := σ.surjective x
      by_cases ha : a.val ≤ m
      · exact no_straddle hσ hz ha i j ⟨hiMin.trans_lt hl', hu'.trans_eq hjMax.symm⟩
      · obtain ⟨k, rfl⟩ := suffix_lift (show m + 1 ≤ a.val by omega)
        exact hx (mem k)
  have hlen : s = hi.val + 1 - lo.val := calc
    s = S.card := by simp [S, Finset.card_image_of_injective _ hf]
    _ = _ := by rw [heq, Fin.card_Icc]
  refine ⟨⟨lo.val - 1, by omega⟩, fun i => ?_⟩
  have hl : lo ≤ f i := S.min'_le _ (mem i)
  have hu : f i ≤ hi := S.le_max' _ (mem i)
  change lo.val - 1 < (f i).val ∧ (f i).val ≤ lo.val - 1 + s
  omega

private theorem exists_assemble {m s : ℕ} (hs : 0 < s) {σ : Perm (m + 1 + s)}
    (hσ : Avoids σ) (hz : (σ (pivot m s)).val = 0) :
    ∃ (t : Fin (m + 1)) (τ : Perm s), assemble t τ = σ := by
  obtain ⟨t, ht⟩ := suffix_interval hs hσ hz
  let f (i : Fin s) : Fin s :=
    ⟨(σ (i.natAdd (m + 1))).val - (t.val + 1), by have := ht i; omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have he := congrArg Fin.val h
    dsimp only [f] at he
    have hi := ht i
    have hj := ht j
    apply Fin.natAdd_injective s (m + 1) (σ.injective (Fin.ext ?_))
    omega
  let τ := Equiv.ofBijective f hf.bijective_of_finite
  refine ⟨t, τ, eq_of_suffix ?_ ?_ ?_⟩
  · simpa only [assemble_left, Fin.rev_rev] using (skip_mono (s := s) t)
  · intro i j hij
    apply descending hσ hz
    · exact Fin.rev_lt_rev.mpr hij
    · change (i.rev).val ≤ m
      omega
  · intro i
    rw [assemble_right]
    apply Fin.ext
    change t.val + 1 + ((σ (i.natAdd (m + 1))).val - (t.val + 1)) = _
    have := ht i
    omega

private theorem assemble_injective {p s : ℕ} (hs : 0 < s) {t u : Fin p} {τ υ : Perm s}
    (h : assemble t τ = assemble u υ) : t = u ∧ τ = υ := by
  have he (i : Fin s) : t.val + 1 + (τ i).val = u.val + 1 + (υ i).val := by
    have := Equiv.congr_fun h (i.natAdd p)
    simpa only [assemble_right, shift, Fin.mk.injEq] using this
  let z : Fin s := ⟨0, hs⟩
  have h₁ := he (τ.symm z)
  have h₂ := he (υ.symm z)
  simp only [Equiv.apply_symm_apply, z, Nat.add_zero] at h₁ h₂
  have htu : t = u := Fin.ext (by omega)
  subst u
  exact ⟨rfl, Equiv.ext fun i => Fin.ext (Nat.add_left_cancel (he i))⟩

private abbrev AtZero (m s : ℕ) :=
  {σ : Perm (m + 1 + s) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧
    σ (pivot m s) = ⟨0, by omega⟩}

private noncomputable def positionEquiv (m s : ℕ) (hs : 0 < s) :
    (Fin (m + 1) × {τ : Perm s // Avoids τ}) ≃ AtZero m s := by
  let f (x : Fin (m + 1) × {τ : Perm s // Avoids τ}) : AtZero m s := by
    obtain ⟨t, τ, hτ⟩ := x
    have h := avoids_assemble t τ hτ
    exact ⟨assemble t τ, h.1, h.2, by simp [pivot, skip]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨t, τ, hτ⟩ ⟨u, υ, hυ⟩ h
    obtain ⟨rfl, rfl⟩ := assemble_injective hs (congrArg Subtype.val h)
    rfl
  · rintro ⟨σ, h₁, h₂, hz⟩
    obtain ⟨t, τ, rfl⟩ := exists_assemble hs ⟨h₁, h₂⟩ (congrArg Fin.val hz)
    exact ⟨⟨t, τ, fun h => h₁ (lift_pattern t τ _ h), fun h => h₂ (lift_pattern t τ _ h)⟩, rfl⟩

end card_avoid_231_3124_pos_zero

/-- **Position of the smallest entry in $(231, 3124)$-avoiding permutations.** For a natural
number $m$, write $S_m(231, 3124)$ for the set of permutations of $\{0, 1, \dots, m-1\}$ that
avoid both patterns $231$ and $3124$, that is, contain neither of them. Let $n \ge 1$ and let
$j$ be a position with $j + 1 < n$. Then the number of permutations $\sigma \in S_n(231, 3124)$
with $\sigma(j) = 0$ equals $(j + 1) \cdot |S_{n-j-1}(231, 3124)|$.

In the source, positions and values start at $1$: with $k = j + 1$, the number of such
permutations with $\sigma(k) = 1$ is $k \cdot |S_{n-k}(231, 3124)|$ for $1 \le k < n$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 11. -/
public theorem card_avoid_231_3124_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} := by
  obtain ⟨m, hm⟩ := j
  change m + 1 < n at hj
  generalize hsize : n - m - 1 = s
  obtain rfl : n = m + 1 + s := by omega
  have hs : 0 < s := by omega
  have h := Nat.card_congr (card_avoid_231_3124_pos_zero.positionEquiv m s hs).symm
  rw [Nat.card_prod, Nat.card_fin] at h
  exact h

namespace card_avoid_231_3124

open card_avoid_231_3124_pos_zero (Avoids Perm descending eq_of_suffix has231_iff has3124_iff)

private theorem card_last (n : ℕ) :
    Nat.card {σ : Perm (n + 1) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ (Fin.last n) = 0} = 1 := by
  have hrev : StrictAnti (@Fin.revPerm (n + 1)) := fun _ _ h => Fin.rev_lt_rev.mpr h
  have havoids : Avoids (@Fin.revPerm (n + 1)) := by
    constructor
    · rw [has231_iff]
      rintro ⟨i, j, k, hij, _, _, hij'⟩
      exact (hrev hij).asymm hij'
    · rw [has3124_iff]
      rintro ⟨i, j, k, l, _, hjk, _, hjk', _, _⟩
      exact (hrev hjk).asymm hjk'
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨Fin.revPerm, havoids.1, havoids.2, by simp⟩, ?_⟩
  intro σ
  apply Subtype.ext
  apply eq_of_suffix (p := n + 1) (s := 0)
  · intro i j hij
    apply descending (m := n) (s := 0) ⟨σ.2.1, σ.2.2.1⟩
    · exact congrArg Fin.val σ.2.2.2
    · exact Fin.rev_lt_rev.mpr hij
    · exact Nat.le_of_lt_succ i.rev.isLt
  · intro i j hij
    exact hrev (Fin.rev_lt_rev.mpr hij)
  · intro i
    exact i.elim0

private abbrev Avoider (n : ℕ) := {σ : Perm n // Avoids σ}

-- Index the count by one less than the number of entries.
private noncomputable def count (n : ℕ) : ℕ := Nat.card (Avoider (n + 1))

private theorem count_eq_sum (n : ℕ) :
    count n = 1 + ∑ k ∈ Finset.range n, (n - k) * count k := by
  let fiber (j : Fin (n + 1)) := {σ : Perm (n + 1) //
    ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ j = ⟨0, Nat.succ_pos n⟩}
  let zeroPos (σ : Avoider (n + 1)) : Fin (n + 1) := σ.1.symm 0
  have e (j : Fin (n + 1)) : {σ // zeroPos σ = j} ≃ fiber j := by
    refine ⟨fun σ => ⟨σ.1.1, σ.1.2.1, σ.1.2.2, ?_⟩,
      fun σ => ⟨⟨σ.1, σ.2.1, σ.2.2.1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · exact (congrArg σ.1.1 σ.2).symm.trans (Equiv.apply_symm_apply _ _)
    · exact (congrArg σ.1.symm σ.2.2.2).symm.trans (Equiv.symm_apply_apply _ _)
  have hsum : count n = ∑ j, Nat.card (fiber j) := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr ((Equiv.sigmaFiberEquiv zeroPos).symm.trans (Equiv.sigmaCongrRight e))
  have hlast : Nat.card (fiber (Fin.last n)) = 1 := card_last n
  rw [hsum, Fin.sum_univ_castSucc, hlast, add_comm]
  congr 1
  calc
    (∑ j : Fin n, Nat.card (fiber j.castSucc)) =
        ∑ j : Fin n, (j.val + 1) * count (n - 1 - j.val) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := card_avoid_231_3124_pos_zero (n + 1) (Nat.succ_pos n) j.castSucc
        (Nat.succ_lt_succ j.isLt)
      change _ = (j.val + 1) * Nat.card (Avoider (n + 1 - j.val - 1)) at h
      rw [show n + 1 - j.val - 1 = (n - 1 - j.val) + 1 by omega] at h
      exact h
    _ = ∑ k ∈ Finset.range n, (k + 1) * count (n - 1 - k) :=
      Fin.sum_univ_eq_sum_range (fun k => (k + 1) * count (n - 1 - k)) n
    _ = ∑ k ∈ Finset.range n, (n - k) * count k := by
      rw [← Finset.sum_range_reflect (fun k => (n - k) * count k) n]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := Finset.mem_range.mp hk
      rw [show n - (n - 1 - k) = k + 1 by omega]

private theorem count_succ (n : ℕ) :
    count (n + 1) = 2 * count n + ∑ k ∈ Finset.range n, count k := by
  have hsum : (∑ k ∈ Finset.range n, (n + 1 - k) * count k) =
      (∑ k ∈ Finset.range n, (n - k) * count k) + ∑ k ∈ Finset.range n, count k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [show n + 1 - k = (n - k) + 1 by omega, add_mul, one_mul]
  have h := count_eq_sum (n + 1)
  rw [Finset.sum_range_succ, Nat.add_sub_cancel_left, one_mul, hsum] at h
  have := count_eq_sum n
  omega

private theorem count_fib : ∀ n : ℕ, count n = Nat.fib (2 * n + 1) := by
  refine Nat.twoStepInduction ?_ ?_ fun n h₀ h₁ => ?_
  · simp [count_eq_sum 0]
  · simp [count_succ 0, count_eq_sum 0, show Nat.fib 3 = 2 by decide]
  · have ha := count_succ n
    have hb : count (n + 2) = 2 * count (n + 1) + ∑ k ∈ Finset.range (n + 1), count k :=
      count_succ (n + 1)
    rw [Finset.sum_range_succ] at hb
    have hf := Nat.fib_add (2 * n + 1) 3
    change Nat.fib (2 * n + 1 + 3 + 1) = Nat.fib (2 * n + 1) * 2 +
      Nat.fib (2 * n + 1 + 1) * 3 at hf
    have hg := Nat.fib_add_two (n := 2 * n + 1)
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega] at h₁
    rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 3 + 1 by omega]
    omega

end card_avoid_231_3124

/-- **$(231, 3124)$-avoiding permutations are counted by odd-indexed Fibonacci numbers.** For
every $n \ge 1$, the number of permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$231$ and $3124$, that is, contain neither of them, is the Fibonacci number $F_{2n-1}$, where
$F_0 = 0$ and $F_1 = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 10. -/
public theorem card_avoid_231_3124 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
      Nat.fib (2 * n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  exact card_avoid_231_3124.count_fib n

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
