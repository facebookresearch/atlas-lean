/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Linarith

/-!
# Fair division of indivisible goods: EF1 via envy-cycle elimination

Agents form a finite type `ι`, goods a finite type `γ`. Valuations `v : ι → γ → ℝ`
are additive: the value of a bundle is the sum of the good values. An allocation
`A : γ → ι` assigns each good to exactly one agent.

Sources: [LMMS04] R. J. Lipton, E. Markakis, E. Mossel and A. Saberi, "On
approximately fair allocations of indivisible goods", Proc. EC 2004, Theorem 2.1
and Lemma 2.2; [BCELP16] F. Brandt et al. (eds.), Handbook of Computational
Social Choice, Cambridge University Press, 2016, Chapter 12.

Clause map (`C1` basic notions, [BCELP16] Ch. 12): `bundle`, `bundleValue`,
`value`, `IsEF`, `IsEF1`, `IsEFX`, `IsProportional`, `maximinShare`,
`IsParetoOptimal`, `nashWelfare`, `bundleValue_empty`, `bundleValue_singleton`,
`isEF_to_isEFX`, `isEFX_to_isEF1`.
Clause map (`C2` envy graph, [LMMS04] proof of Theorem 2.1, [BCELP16] Ch. 12):
`Envy`, `IsSource`, `IsEnvyCycle`, `HasEnvyCycle`, `walk_contains_cycle`,
`exists_source_of_acyclic`.
Clause map (`C3` cycle rotation, [LMMS04] Lemma 2.2): `rotateAlloc`,
`bundle_rotate_onCycle`, `bundle_rotate_offCycle`, `rotate_value_le`,
`rotate_value_lt_onCycle`, `rotate_isEF1`.
Clause map (`C4` main theorem, [LMMS04] Theorem 2.1): `socialWelfare`,
`extendAlloc`, `extend_isEF1`, `exists_EF1_acyclic`, `exists_EF1_subtype`,
`ef1_existence`.
Clause map (`C5` bounded envy, [LMMS04] Theorem 2.1, [BCELP16] Ch. 12):
`ef1_envy_gap`, `bounded_envy_existence`.
Clause map (`C6` separating examples, [BCELP16] Ch. 12): `exA_val`, `exA_alloc`,
`exB_val`, `exB_alloc` (verdicts live in the test module).

Non-goals: existence of EFX allocations for three or more agents (an open
problem) is not claimed; maximin-share approximation guarantees are not proved.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.GameTheory.FairDivision.Indivisible

open Classical

/-- Bundle of agent `i`: the finset of goods assigned to `i` by `A`. -/
def bundle {ι γ : Type*} [Fintype γ] [DecidableEq ι] (A : γ → ι) (i : ι) :
    Finset γ :=
  Finset.univ.filter (fun g => A g = i)

/-- Value of a bundle `B` to agent `i`: the finset sum of `v i` over `B`. -/
def bundleValue {ι γ : Type*} (v : ι → γ → ℝ) (i : ι) (B : Finset γ) : ℝ :=
  ∑ g ∈ B, v i g

/-- Value of agent `i`'s own bundle under allocation `A`. -/
def value {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) (i : ι) : ℝ :=
  bundleValue v i (bundle A i)

/-- Envy-freeness: every agent values its own bundle at least as much as any
other agent's bundle. -/
def IsEF {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) : Prop :=
  ∀ i j, bundleValue v i (bundle A j) ≤ value v A i

/-- Envy-freeness up to one good: for all `i j`, if `j`'s bundle is nonempty
then some good can be removed from it so that `i` does not envy the remainder. -/
def IsEF1 {ι γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : Prop :=
  ∀ i j, (bundle A j).Nonempty →
    ∃ g ∈ bundle A j, bundleValue v i ((bundle A j).erase g) ≤ value v A i

/-- Envy-freeness up to any good: removing any single good from `j`'s bundle
removes `i`'s envy. -/
def IsEFX {ι γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : Prop :=
  ∀ i j, ∀ g ∈ bundle A j,
    bundleValue v i ((bundle A j).erase g) ≤ value v A i

/-- Proportionality: each agent gets at least a `1 / card ι` share of its
value for all goods, stated without division. The universal form also covers
the empty-agent case vacuously. -/
def IsProportional {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : Prop :=
  ∀ i, ∑ g, v i g ≤ (Fintype.card ι : ℝ) * value v A i

/-- Maximin share of agent `i`: the best worst-bundle value `i` can guarantee
by choosing the allocation, as a finset maximum over all allocations `A` of
the finset minimum over agents `j` of `bundleValue v i (bundle A j)`. -/
noncomputable def maximinShare {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ) (i : ι) : ℝ :=
  haveI : Nonempty (γ → ι) := ⟨fun _ => Classical.choice inferInstance⟩
  (Finset.univ.image (fun A : γ → ι =>
    (Finset.univ.image (fun j : ι => bundleValue v i (bundle A j))).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty))).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Pareto optimality: no other allocation weakly improves every agent and
strictly improves one of them. -/
def IsParetoOptimal {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : Prop :=
  ¬ ∃ B : γ → ι, (∀ i, value v A i ≤ value v B i) ∧
    ∃ i, value v A i < value v B i

/-- Nash welfare of an allocation: the product of the agents' bundle values. -/
def nashWelfare {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : ℝ :=
  ∏ i, value v A i

/-- Bundle value of the empty bundle is `0`. -/
theorem bundleValue_empty {ι γ : Type*} (v : ι → γ → ℝ) (i : ι) :
    bundleValue v i ∅ = 0 :=
  Finset.sum_empty

/-- Bundle value of a singleton bundle is the good's value. -/
theorem bundleValue_singleton {ι γ : Type*} (v : ι → γ → ℝ) (i : ι) (g : γ) :
    bundleValue v i {g} = v i g :=
  Finset.sum_singleton _ _

/-- Envy-freeness implies envy-freeness up to any good, for nonnegative
valuations. Nonnegativity is needed: removing a negatively-valued good can
create envy. -/
theorem isEF_to_isEFX {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι)
    (hv : ∀ i g, 0 ≤ v i g) (h : IsEF v A) : IsEFX v A := by
  intro i j g hg
  have h1 := h i j
  have he := Finset.add_sum_erase (bundle A j) (v i) hg
  have hnn : 0 ≤ v i g := hv i g
  have h2 : bundleValue v i ((bundle A j).erase g) ≤
      bundleValue v i (bundle A j) := by
    unfold bundleValue
    have hle : ∑ x ∈ (bundle A j).erase g, v i x ≤
        v i g + ∑ x ∈ (bundle A j).erase g, v i x :=
      le_add_of_nonneg_left hnn
    rwa [he] at hle
  exact le_trans h2 h1

/-- Envy-freeness up to any good implies envy-freeness up to one good. -/
theorem isEFX_to_isEF1 {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι) (h : IsEFX v A) : IsEF1 v A := by
  intro i j hne
  obtain ⟨g, hg⟩ := hne
  exact ⟨g, hg, h i j g hg⟩

/-- Envy: agent `i` strictly prefers `j`'s bundle to its own bundle. -/
def Envy {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) (i j : ι) : Prop :=
  value v A i < bundleValue v i (bundle A j)

/-- Source of the envy graph: an agent nobody envies. -/
def IsSource {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) (i : ι) : Prop :=
  ∀ j, ¬ Envy v A j i

/-- An explicit envy cycle of length `m`: an injective indexing `c` with envy
edges `c t → c (t + 1)` for all `t`. Indexing by `ZMod m` makes the
wraparound edge ordinary ring arithmetic. -/
def IsEnvyCycle {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) (m : ℕ) (c : ZMod m → ι) : Prop :=
  2 ≤ m ∧ Function.Injective c ∧ ∀ t : ZMod m, Envy v A (c t) (c (t + 1))

/-- The envy graph has a directed cycle. -/
def HasEnvyCycle {ι γ : Type*} [Fintype γ] [DecidableEq ι] (v : ι → γ → ℝ)
    (A : γ → ι) : Prop :=
  ∃ m c, IsEnvyCycle v A m c

/-- A closed envy walk of positive length contains an explicit envy cycle: by strong induction on
the length, either the walk is already injective or a repeated agent splits
it into strictly shorter closed walks. -/
theorem walk_contains_cycle {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) (n : ℕ) (p : ℕ → ι)
    (hedge : ∀ k < n, Envy v A (p k) (p (k + 1))) (hclose : p n = p 0)
    (hpos : 1 ≤ n) : ∃ m c, IsEnvyCycle v A m c := by
  have H : ∀ (n : ℕ) (p : ℕ → ι),
      (∀ k < n, Envy v A (p k) (p (k + 1))) →
      p n = p 0 → 1 ≤ n → ∃ m c, IsEnvyCycle v A m c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro p hedge hclose hpos
      by_cases hdist : ∀ i < n, ∀ j < n, i ≠ j → p i ≠ p j
      · have hn1 : n ≠ 1 := by
          rintro rfl
          have h0 := hedge 0 (by omega)
          change Envy v A (p 0) (p 1) at h0
          rw [hclose] at h0
          unfold Envy at h0
          exact (lt_irrefl _ h0).elim
        have hn2 : 2 ≤ n := by omega
        have : NeZero n := ⟨by omega⟩
        refine ⟨n, fun t => p t.val, hn2, ?_, ?_⟩
        · intro a b hab
          dsimp only at hab
          have ha : a.val < n := ZMod.val_lt a
          have hb : b.val < n := ZMod.val_lt b
          have hval : a.val = b.val := by
            by_contra hne
            exact absurd hab (hdist _ ha _ hb hne)
          exact ZMod.val_injective n hval
        · intro t
          dsimp only
          have htn : t.val < n := ZMod.val_lt t
          have ht : t = ((t.val : ℕ) : ZMod n) := by
            have h := ZMod.natCast_val (R := ZMod n) t
            rw [ZMod.cast_id] at h
            exact h.symm
          by_cases hwr : t.val + 1 < n
          · have hcast : t + 1 = (((t.val + 1 : ℕ)) : ZMod n) := by
              conv_lhs => rw [ht]
              rw [Nat.cast_add, Nat.cast_one]
            have hval : (t + 1).val = t.val + 1 := by
              rw [hcast]
              exact ZMod.val_natCast_of_lt hwr
            rw [hval]
            exact hedge _ htn
          · have h1 : t.val + 1 = n := by omega
            have hcast : t + 1 = (0 : ZMod n) := by
              have e1 : ((t.val : ℕ) : ZMod n) + 1
                  = (((t.val + 1 : ℕ)) : ZMod n) := by
                rw [Nat.cast_add, Nat.cast_one]
              rw [ht, e1, h1, ZMod.natCast_self]
            have hval : (t + 1).val = 0 := by
              rw [hcast, ZMod.val_zero]
            rw [hval]
            have hnm : n - 1 < n := by omega
            have h2 := hedge (n - 1) hnm
            have h3 : n - 1 + 1 = n := by omega
            rw [h3, hclose] at h2
            have h4 : t.val = n - 1 := by omega
            rw [h4]
            exact h2
      · have hex : ∃ i, i < n ∧ ∃ j, j < n ∧ i ≠ j ∧ p i = p j := by
          by_contra hcon
          apply hdist
          intro i hi j hj hne heq
          apply hcon
          exact ⟨i, hi, j, hj, hne, heq⟩
        obtain ⟨i, hi, j, hj, hne, heq⟩ := hex
        have hlt : min i j < max i j := by
          rcases lt_or_gt_of_ne hne with h | h
          · rw [min_eq_left h.le, max_eq_right h.le]
            exact h
          · rw [min_eq_right h.le, max_eq_left h.le]
            exact h
        have hmax : max i j < n := max_lt hi hj
        have heq' : p (min i j) = p (max i j) := by
          rcases lt_or_gt_of_ne hne with h | h
          · rw [min_eq_left h.le, max_eq_right h.le]
            exact heq
          · rw [min_eq_right h.le, max_eq_left h.le]
            exact heq.symm
        have hlen : max i j - min i j < n := by omega
        have hpos' : 1 ≤ max i j - min i j := by omega
        refine IH _ hlen (fun k => p (min i j + k)) ?_ ?_ hpos'
        · intro k hk
          show Envy v A (p (min i j + k)) (p (min i j + (k + 1)))
          have h1 : min i j + k < n := by omega
          have h2 : min i j + (k + 1) = (min i j + k) + 1 := by omega
          rw [h2]
          exact hedge _ h1
        · show p (min i j + (max i j - min i j)) = p (min i j)
          have hsub : min i j + (max i j - min i j) = max i j := by omega
          rw [hsub]
          exact heq'.symm
  exact H n p hedge hclose hpos

/-- If the envy graph on a nonempty finite agent type has no directed cycle
(stated as the absence of an explicit `ZMod`-indexed cycle, the same form
`C4` discharges after cycle elimination), then a source exists: otherwise
iterating envy witnesses repeats an agent, giving a closed walk. -/
theorem exists_source_of_acyclic {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ) (A : γ → ι)
    (h : ¬ HasEnvyCycle v A) : ∃ i, IsSource v A i := by
  by_contra hcon
  have henv : ∀ i, ∃ j, Envy v A j i := by
    intro i
    by_contra hi
    apply hcon
    refine ⟨i, ?_⟩
    intro j hEj
    apply hi
    exact ⟨j, hEj⟩
  choose f hf using henv
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hc : (Finset.univ : Finset ι).card
      < (Finset.range (Fintype.card ι + 1)).card := by
    rw [Finset.card_range]
    have hcard : (Finset.univ : Finset ι).card = Fintype.card ι := rfl
    omega
  have hmaps : Set.MapsTo (fun k => f^[k] i₀)
      ↑(Finset.range (Fintype.card ι + 1)) ↑(Finset.univ : Finset ι) :=
    fun k _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  obtain ⟨a, ha, b, hb, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  have hlt : min a b < max a b := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]
      exact h
    · rw [min_eq_right h.le, max_eq_left h.le]
      exact h
  have heq' : f^[min a b] i₀ = f^[max a b] i₀ := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]
      exact heq
    · rw [min_eq_right h.le, max_eq_left h.le]
      exact heq.symm
  have hpos' : 1 ≤ max a b - min a b := by omega
  have hedge' : ∀ k < max a b - min a b,
      Envy v A (f^[max a b - k] i₀) (f^[max a b - (k + 1)] i₀) := by
    intro k hk
    have hkm : max a b - k = (max a b - (k + 1)).succ := by omega
    rw [hkm, Function.iterate_succ_apply']
    exact hf _
  have hclose' : f^[max a b - (max a b - min a b)] i₀
      = f^[max a b - 0] i₀ := by
    have hsub : max a b - (max a b - min a b) = min a b := by omega
    rw [hsub, Nat.sub_zero]
    exact heq'
  have hcon2 := walk_contains_cycle v A (max a b - min a b)
    (fun k => f^[max a b - k] i₀) hedge' hclose' hpos'
  exact h hcon2

/-- Rotation along `c`, defined for any `c`: a good whose owner is `c t` for a chosen preimage `t`
moves to `c (t - 1)`, and goods held by agents outside the image of `c` stay put. For an
injective `c`, such as an envy cycle, every agent on it receives the bundle of its successor. -/
noncomputable def rotateAlloc {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (m : ℕ) (c : ZMod m → ι) (A : γ → ι) (hm : 2 ≤ m) : γ → ι :=
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty (ZMod m) := ⟨0⟩
  fun g =>
    if _ : A g ∈ Finset.univ.image c then c (Function.invFun c (A g) - 1)
    else A g

/-- Under rotation, an agent on the cycle receives its successor's bundle. -/
theorem bundle_rotate_onCycle {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (A : γ → ι) (m : ℕ) (c : ZMod m → ι) (hm : 2 ≤ m)
    (hinj : Function.Injective c) (t : ZMod m) :
    bundle (rotateAlloc m c A hm) (c t) = bundle A (c (t + 1)) := by
  have : NeZero m := ⟨by omega⟩
  have : Nonempty (ZMod m) := ⟨0⟩
  ext g
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [rotateAlloc]
  by_cases hmem : A g ∈ Finset.univ.image c
  · simp only [dite_eq_left hmem]
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hmem
    have hidx : Function.invFun c (A g) = s :=
      hinj ((Function.invFun_eq ⟨s, hs⟩).trans hs.symm)
    rw [hidx]
    constructor
    · intro hcon
      have hst : s = t + 1 := sub_eq_iff_eq_add.mp (hinj hcon)
      rw [← hs, hst]
    · intro hcon
      have hst : s = t + 1 := hinj (hs.trans hcon)
      have hsub : s - 1 = t := by rw [hst]; exact sub_eq_iff_eq_add.mpr rfl
      rw [hsub]
  · simp only [dite_eq_right hmem]
    constructor
    · intro hcon
      exact absurd (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, hcon.symm⟩)
        hmem
    · intro hcon
      exact absurd
        (Finset.mem_image.mpr ⟨t + 1, Finset.mem_univ _, hcon.symm⟩) hmem

/-- Under rotation, agents off the cycle keep their bundle. -/
theorem bundle_rotate_offCycle {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (A : γ → ι) (m : ℕ) (c : ZMod m → ι) (hm : 2 ≤ m)
    (x : ι) (hx : ∀ a, c a ≠ x) :
    bundle (rotateAlloc m c A hm) x = bundle A x := by
  have : NeZero m := ⟨by omega⟩
  ext g
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [rotateAlloc]
  by_cases hmem : A g ∈ Finset.univ.image c
  · simp only [dite_eq_left hmem]
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hmem
    have hL : c (Function.invFun c (A g) - 1) ≠ x := hx _
    have hR : A g ≠ x := by rw [← hs]; exact hx s
    exact ⟨fun h => (hL h).elim, fun h => (hR h).elim⟩
  · rw [dite_eq_right hmem]

/-- Every agent's own-bundle value weakly increases under rotation. -/
theorem rotate_value_le {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) (m : ℕ) (c : ZMod m → ι) (hm : 2 ≤ m)
    (hinj : Function.Injective c)
    (hedge : ∀ t : ZMod m, Envy v A (c t) (c (t + 1))) (x : ι) :
    value v A x ≤ value v (rotateAlloc m c A hm) x := by
  by_cases h : ∃ t, c t = x
  · obtain ⟨t, rfl⟩ := h
    have hrot := bundle_rotate_onCycle A m c hm hinj t
    unfold value
    rw [hrot]
    exact le_of_lt (hedge t)
  · have hx : ∀ a, c a ≠ x := fun a ha => h ⟨a, ha⟩
    have hrot := bundle_rotate_offCycle A m c hm x hx
    have heq : value v (rotateAlloc m c A hm) x = value v A x := by
      unfold value
      rw [hrot]
    exact heq.ge

/-- Agents on the cycle strictly increase their own-bundle value. -/
theorem rotate_value_lt_onCycle {ι γ : Type*} [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) (m : ℕ) (c : ZMod m → ι) (hm : 2 ≤ m)
    (hinj : Function.Injective c)
    (hedge : ∀ t : ZMod m, Envy v A (c t) (c (t + 1))) (t : ZMod m) :
    value v A (c t) < value v (rotateAlloc m c A hm) (c t) := by
  have hrot := bundle_rotate_onCycle A m c hm hinj t
  unfold value
  rw [hrot]
  exact hedge t

/-- Rotation preserves EF1: bundles are only permuted, and no agent's own
bundle loses value, so every EF1 witness still works. -/
theorem rotate_isEF1 {ι γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) (m : ℕ) (c : ZMod m → ι) (hm : 2 ≤ m)
    (hinj : Function.Injective c)
    (hedge : ∀ t : ZMod m, Envy v A (c t) (c (t + 1))) (h : IsEF1 v A) :
    IsEF1 v (rotateAlloc m c A hm) := by
  intro i j hjne
  by_cases hj : ∃ t, c t = j
  · obtain ⟨t, rfl⟩ := hj
    have hrot := bundle_rotate_onCycle A m c hm hinj t
    rw [hrot] at hjne
    rw [hrot]
    obtain ⟨g, hg, hle⟩ := h i (c (t + 1)) hjne
    exact ⟨g, hg, le_trans hle (rotate_value_le v A m c hm hinj hedge i)⟩
  · have hx : ∀ a, c a ≠ j := fun a ha => hj ⟨a, ha⟩
    have hrot := bundle_rotate_offCycle A m c hm j hx
    rw [hrot] at hjne
    rw [hrot]
    obtain ⟨g, hg, hle⟩ := h i j hjne
    exact ⟨g, hg, le_trans hle (rotate_value_le v A m c hm hinj hedge i)⟩

/-- Social welfare of an allocation: the sum of the agents' own-bundle values.
Cycle rotation strictly increases it, driving cycle elimination. -/
def socialWelfare {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (A : γ → ι) : ℝ :=
  ∑ i, value v A i

/-- From any EF1 allocation, some EF1 allocation has an acyclic envy graph:
take an EF1 allocation of maximal social welfare, which cannot admit a
rotation. Finiteness of the allocation set gives the maximizer. -/
theorem exists_EF1_acyclic {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] (v : ι → γ → ℝ) (A : γ → ι)
    (hA : IsEF1 v A) : ∃ A' : γ → ι, IsEF1 v A' ∧ ¬ HasEnvyCycle v A' := by
  have hAT : A ∈ Finset.univ.filter (fun B : γ → ι => IsEF1 v B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ A, hA⟩
  have hTne : (Finset.univ.filter (fun B : γ → ι => IsEF1 v B)).Nonempty :=
    ⟨A, hAT⟩
  have hWne : ((Finset.univ.filter (fun B : γ → ι => IsEF1 v B)).image
      (fun B => socialWelfare v B)).Nonempty := by
    obtain ⟨B, hB⟩ := hTne
    exact ⟨socialWelfare v B, Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩
  obtain ⟨B, hBT, hBmax⟩ := Finset.mem_image.mp (Finset.max'_mem _ hWne)
  have hBef1 : IsEF1 v B := (Finset.mem_filter.mp hBT).2
  refine ⟨B, hBef1, ?_⟩
  rintro ⟨m, c, hm, hinj, hedge⟩
  have hB'T : rotateAlloc m c B hm ∈
      Finset.univ.filter (fun B : γ → ι => IsEF1 v B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      rotate_isEF1 v B m c hm hinj hedge hBef1⟩
  have hle : socialWelfare v (rotateAlloc m c B hm) ≤
      ((Finset.univ.filter (fun B : γ → ι => IsEF1 v B)).image
        (fun B => socialWelfare v B)).max' hWne :=
    Finset.le_max' _ _
      (Finset.mem_image.mpr ⟨rotateAlloc m c B hm, hB'T, rfl⟩)
  have hlt : socialWelfare v B <
      socialWelfare v (rotateAlloc m c B hm) := by
    unfold socialWelfare
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨c 0, Finset.mem_univ _, ?_⟩
    · exact rotate_value_le v B m c hm hinj hedge i
    · exact rotate_value_lt_onCycle v B m c hm hinj hedge 0
  rw [hBmax] at hlt
  exact absurd hle (not_le_of_gt hlt)

/-- Extend a partial allocation (on goods `↥S`) with a good `g`, giving `g` to agent `i₀`
(even if `g ∈ S`) and keeping every other good's holder. -/
def extendAlloc {ι γ : Type*} [DecidableEq γ] (S : Finset γ) (g : γ)
    (A : ↥S → ι) (i₀ : ι) : ↥(insert g S) → ι :=
  fun x =>
    if h : x.val = g then i₀
    else A ⟨x.val, (Finset.mem_insert.mp x.property).resolve_left h⟩

private def extendEmb {γ : Type*} [DecidableEq γ] (S : Finset γ) (g : γ) :
    ↥S ↪ ↥(insert g S) :=
  ⟨fun y => ⟨y.val, Finset.mem_insert_of_mem y.property⟩, by
    intro a b h
    dsimp only at h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h⟩

private theorem extendEmb_val {γ : Type*} [DecidableEq γ] (S : Finset γ)
    (g : γ) (y : ↥S) : (extendEmb S g y).val = y.val := rfl

private theorem bundle_extend_of_ne {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (S : Finset γ) (g : γ) (hg : g ∉ S) (A : ↥S → ι)
    (i₀ j : ι) (hj : j ≠ i₀) :
    bundle (extendAlloc S g A i₀) j = (bundle A j).map (extendEmb S g) := by
  ext x
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  simp only [extendAlloc]
  by_cases hx : x.val = g
  · simp only [dite_eq_left hx]
    constructor
    · intro hcon
      exact absurd hcon.symm hj
    · rintro ⟨y, hy, hxy⟩
      have h3 := congrArg Subtype.val hxy
      rw [extendEmb_val, hx] at h3
      have h4 := y.property
      rw [h3] at h4
      exact absurd h4 hg
  · simp only [dite_eq_right hx]
    constructor
    · intro hcon
      exact ⟨_, hcon, Subtype.ext rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have h2 : ⟨x.val, (Finset.mem_insert.mp x.property).resolve_left hx⟩
          = y := by
        apply Subtype.ext
        show x.val = y.val
        have h3 := congrArg Subtype.val hxy
        rw [extendEmb_val] at h3
        exact h3.symm
      rw [h2]
      exact hy

private theorem bundle_extend_self {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (S : Finset γ) (g : γ) (A : ↥S → ι)
    (i₀ : ι) :
    bundle (extendAlloc S g A i₀) i₀
      = insert ⟨g, Finset.mem_insert_self g S⟩
        ((bundle A i₀).map (extendEmb S g)) := by
  ext x
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Finset.mem_insert]
  simp only [extendAlloc]
  by_cases hx : x.val = g
  · simp only [dite_eq_left hx]
    constructor
    · intro _
      left
      apply Subtype.ext
      exact hx
    · intro _
      trivial
  · simp only [dite_eq_right hx]
    constructor
    · intro hcon
      right
      exact ⟨_, hcon, Subtype.ext rfl⟩
    · rintro (rfl | ⟨y, hy, hxy⟩)
      · exfalso
        apply hx
        rfl
      · have h2 : ⟨x.val, (Finset.mem_insert.mp x.property).resolve_left hx⟩
            = y := by
          apply Subtype.ext
          show x.val = y.val
          have h3 := congrArg Subtype.val hxy
          rw [extendEmb_val] at h3
          exact h3.symm
        rw [h2]
        exact hy

private theorem sum_map_extend {ι γ : Type*} [DecidableEq γ]
    (v : ι → γ → ℝ) (S : Finset γ) (g : γ) (i : ι) (B : Finset ↥S) :
    ∑ x ∈ B.map (extendEmb S g), (fun i x => v i x.val) i x
      = ∑ y ∈ B, (fun i x => v i x.val) i y := by
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rfl

private theorem value_extend_le {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (v : ι → γ → ℝ) (hv : ∀ i g, 0 ≤ v i g) (S : Finset γ)
    (g : γ) (hg : g ∉ S) (A : ↥S → ι) (i₀ i : ι) :
    value (fun i x => v i x.val) A i
      ≤ value (fun i x => v i x.val) (extendAlloc S g A i₀) i := by
  by_cases hi : i = i₀
  · subst hi
    have hrot := bundle_extend_self S g A i
    have hxg : (⟨g, Finset.mem_insert_self g S⟩ : ↥(insert g S))
        ∉ (bundle A i).map (extendEmb S g) := by
      intro hcon
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hcon
      have h3 : y.val = g := by
        have h4 := congrArg Subtype.val hxy
        rw [extendEmb_val] at h4
        have h5 : (⟨g, Finset.mem_insert_self g S⟩ : ↥(insert g S)).val
            = g := rfl
        rw [h5] at h4
        exact h4
      have h4 := y.property
      rw [h3] at h4
      exact hg h4
    unfold value bundleValue
    rw [hrot, Finset.sum_insert hxg, sum_map_extend]
    exact le_add_of_nonneg_left (hv i g)
  · have hrot := bundle_extend_of_ne S g hg A i₀ i hi
    have heq : value (fun i x => v i x.val) (extendAlloc S g A i₀) i
        = value (fun i x => v i x.val) A i := by
      unfold value bundleValue
      rw [hrot, sum_map_extend]
    exact heq.ge

/-- Giving a new good to a source preserves EF1: only the source's bundle
grows, and removing the new good restores the old comparison. -/
theorem extend_isEF1 {ι γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (hv : ∀ i g, 0 ≤ v i g) (S : Finset γ) (g : γ)
    (hg : g ∉ S) (A : ↥S → ι) (i₀ : ι)
    (hA : IsEF1 (fun i x => v i x.val) A)
    (hsrc : IsSource (fun i x => v i x.val) A i₀) :
    IsEF1 (fun i x => v i x.val) (extendAlloc S g A i₀) := by
  intro i j hjne
  by_cases hj : j = i₀
  · subst hj
    have hrot := bundle_extend_self S g A j
    have hxgmem : (⟨g, Finset.mem_insert_self g S⟩ : ↥(insert g S))
        ∈ bundle (extendAlloc S g A j) j := by
      rw [hrot]
      exact Finset.mem_insert_self _ _
    have hxg : (⟨g, Finset.mem_insert_self g S⟩ : ↥(insert g S))
        ∉ (bundle A j).map (extendEmb S g) := by
      intro hcon
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hcon
      have h3 : y.val = g := by
        have h4 := congrArg Subtype.val hxy
        rw [extendEmb_val] at h4
        have h5 : (⟨g, Finset.mem_insert_self g S⟩ : ↥(insert g S)).val
            = g := rfl
        rw [h5] at h4
        exact h4
      have h4 := y.property
      rw [h3] at h4
      exact hg h4
    have herase : (bundle (extendAlloc S g A j) j).erase
        ⟨g, Finset.mem_insert_self g S⟩
        = (bundle A j).map (extendEmb S g) := by
      rw [hrot]
      exact Finset.erase_insert hxg
    have hle0 : bundleValue (fun i x => v i x.val) i (bundle A j)
        ≤ value (fun i x => v i x.val) A i := by
      have hnsrc := hsrc i
      unfold Envy at hnsrc
      exact le_of_not_gt hnsrc
    refine ⟨⟨g, Finset.mem_insert_self g S⟩, hxgmem, ?_⟩
    rw [herase]
    have hmap := sum_map_extend v S g i (bundle A j)
    unfold bundleValue
    rw [hmap]
    have hle1 : ∑ x ∈ bundle A j, (fun i x => v i x.val) i x
        ≤ value (fun i x => v i x.val) A i := hle0
    exact le_trans hle1 (value_extend_le v hv S g hg A j i)
  · have hrot := bundle_extend_of_ne S g hg A i₀ j hj
    rw [hrot] at hjne
    have hjne' : (bundle A j).Nonempty := by
      obtain ⟨x, hx⟩ := hjne
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨y, hy⟩
    obtain ⟨y₀, hy₀, hle⟩ := hA i j hjne'
    have hmem : extendEmb S g y₀ ∈ bundle (extendAlloc S g A i₀) j := by
      rw [hrot]
      exact Finset.mem_map.mpr ⟨y₀, hy₀, rfl⟩
    have herase : (bundle (extendAlloc S g A i₀) j).erase (extendEmb S g y₀)
        = ((bundle A j).erase y₀).map (extendEmb S g) := by
      rw [hrot, ← Finset.map_erase]
    refine ⟨extendEmb S g y₀, hmem, ?_⟩
    rw [herase]
    have hmap := sum_map_extend v S g i ((bundle A j).erase y₀)
    unfold bundleValue
    rw [hmap]
    have hle1 : ∑ x ∈ (bundle A j).erase y₀, (fun i x => v i x.val) i x
        ≤ value (fun i x => v i x.val) A i := hle
    exact le_trans hle1 (value_extend_le v hv S g hg A i₀ i)

/-- For every finset `S` of goods there is an EF1 allocation of `↥S`, by
induction on `S`: purify the induction hypothesis, extend at a source. -/
theorem exists_EF1_subtype {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (S : Finset γ) :
    ∃ A : ↥S → ι, IsEF1 (fun i x => v i x.val) A := by
  induction S using Finset.induction with
  | empty =>
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    refine ⟨fun _ => i₀, ?_⟩
    intro i j hne
    obtain ⟨x, hx⟩ := hne
    exact absurd x.property (Finset.notMem_empty _)
  | insert g S hg ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨A2, hA2ef1, hA2acyc⟩ :=
      exists_EF1_acyclic (fun i x => v i x.val) A hA
    obtain ⟨i₀, hsrc⟩ :=
      exists_source_of_acyclic (fun i x => v i x.val) A2 hA2acyc
    exact ⟨extendAlloc S g A2 i₀,
      extend_isEF1 v hv S g hg A2 i₀ hA2ef1 hsrc⟩

private def univEmb {γ : Type*} [Fintype γ] [DecidableEq γ] :
    ↥(Finset.univ : Finset γ) ↪ γ :=
  ⟨fun y => y.val, by
    intro a b h
    dsimp only at h
    exact Subtype.ext h⟩

private theorem univEmb_val {γ : Type*} [Fintype γ] [DecidableEq γ]
    (y : ↥(Finset.univ : Finset γ)) : univEmb y = y.val := rfl

private theorem bundle_univ_transport {ι γ : Type*} [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] (A0 : ↥(Finset.univ : Finset γ) → ι)
    (j : ι) :
    bundle (fun g => A0 ⟨g, Finset.mem_univ g⟩) j
      = (bundle A0 j).map univEmb := by
  ext g
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · intro hcon
    exact ⟨⟨g, Finset.mem_univ g⟩, hcon, univEmb_val _⟩
  · rintro ⟨y, hy, hxy⟩
    have h2 : (⟨g, Finset.mem_univ g⟩ : ↥(Finset.univ : Finset γ)) = y := by
      apply Subtype.ext
      show g = y.val
      have h3 : y.val = g := hxy
      exact h3.symm
    rw [h2]
    exact hy

private theorem sum_map_univ {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    (v : ι → γ → ℝ) (i : ι) (B : Finset ↥(Finset.univ : Finset γ)) :
    ∑ x ∈ B.map univEmb, v i x
      = ∑ y ∈ B, (fun i x => v i x.val) i y := by
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rfl

/-- EF1 allocations always exist for additive nonnegative valuations, by
envy-cycle elimination. Partial allocations are total allocations on subtype
goods `↥S`; the final transport takes `S` to be all goods. The `[Nonempty ι]`
hypothesis is load-bearing: with no agents and a nonempty good type there is
no allocation at all, so the unguarded existence claim is false. -/
theorem ef1_existence {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : γ → ι, IsEF1 v A := by
  obtain ⟨A0, hA0⟩ := exists_EF1_subtype v hv Finset.univ
  refine ⟨fun g => A0 ⟨g, Finset.mem_univ g⟩, ?_⟩
  intro i j hjne
  have hrot := bundle_univ_transport A0 j
  rw [hrot] at hjne
  have hjne' : (bundle A0 j).Nonempty := by
    obtain ⟨x, hx⟩ := hjne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact ⟨y, hy⟩
  obtain ⟨y₀, hy₀, hle⟩ := hA0 i j hjne'
  have hmem : univEmb y₀ ∈ bundle (fun g => A0 ⟨g, Finset.mem_univ g⟩) j := by
    rw [hrot]
    exact Finset.mem_map.mpr ⟨y₀, hy₀, rfl⟩
  have herase : (bundle (fun g => A0 ⟨g, Finset.mem_univ g⟩) j).erase
      (univEmb y₀) = ((bundle A0 j).erase y₀).map univEmb := by
    rw [hrot, ← Finset.map_erase]
  refine ⟨univEmb y₀, hmem, ?_⟩
  rw [herase]
  have hmap := sum_map_univ v i ((bundle A0 j).erase y₀)
  unfold bundleValue
  rw [hmap]
  have hval : value v (fun g => A0 ⟨g, Finset.mem_univ g⟩) i
      = value (fun i x => v i x.val) A0 i := by
    unfold value bundleValue
    rw [bundle_univ_transport, sum_map_univ]
  have hle1 : ∑ x ∈ (bundle A0 j).erase y₀, (fun i x => v i x.val) i x
      ≤ value (fun i x => v i x.val) A0 i := hle
  rw [hval]
  exact hle1

/-- In an EF1 allocation, any envy is bounded by a single good's value: the
EF1 witness `g` satisfies the gap inequality. -/
theorem ef1_envy_gap {ι γ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    (v : ι → γ → ℝ) (hv : ∀ i g, 0 ≤ v i g) (A : γ → ι) (h : IsEF1 v A)
    (i j : ι) (henvy : Envy v A i j) :
    ∃ g ∈ bundle A j, bundleValue v i ((bundle A j).erase g) ≤ value v A i ∧
      bundleValue v i (bundle A j) - value v A i ≤ v i g := by
  have hne : (bundle A j).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    unfold Envy at henvy
    rw [hcon, bundleValue_empty] at henvy
    have hnn : 0 ≤ value v A i := by
      unfold value bundleValue
      exact Finset.sum_nonneg (fun g _ => hv i g)
    exact absurd hnn (not_le_of_gt henvy)
  obtain ⟨g, hg, hle⟩ := h i j hne
  refine ⟨g, hg, hle, ?_⟩
  have he := Finset.add_sum_erase (bundle A j) (v i) hg
  unfold bundleValue at hle ⊢
  linarith

/-- Some allocation has all envy bounded by a single good's value. -/
theorem bounded_envy_existence {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] [Nonempty ι] (v : ι → γ → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : γ → ι, ∀ i j, Envy v A i j →
      ∃ g ∈ bundle A j, bundleValue v i ((bundle A j).erase g) ≤ value v A i ∧
        bundleValue v i (bundle A j) - value v A i ≤ v i g := by
  obtain ⟨A, hA⟩ := ef1_existence v hv
  exact ⟨A, fun i j henv => ef1_envy_gap v hv A hA i j henv⟩

/-- Separating example (a) valuations: agent 0 values every good at 1, agent 1
values good 3 at 3 and the rest at 1. -/
def exA_val : Fin 2 → Fin 4 → ℝ :=
  fun i g => if i.val = 1 ∧ g.val = 3 then 3 else 1

/-- Separating example (a) allocation: goods `{2, 3}` to agent 0, goods
`{0, 1}` to agent 1. -/
def exA_alloc : Fin 4 → Fin 2 :=
  fun g => if g.val = 2 ∨ g.val = 3 then 0 else 1

/-- Separating example (b) valuations: both agents value good 0 at 3 and
good 1 at 2. -/
def exB_val : Fin 2 → Fin 2 → ℝ :=
  fun _ g => if g.val = 0 then 3 else 2

/-- Separating example (b) allocation: good 0 to agent 0, good 1 to agent 1. -/
def exB_alloc : Fin 2 → Fin 2 :=
  fun g => g

end MathlibExt.GameTheory.FairDivision.Indivisible

end
