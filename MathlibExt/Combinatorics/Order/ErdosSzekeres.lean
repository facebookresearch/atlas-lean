/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-!
# Erdős–Szekeres monotone subsequence theorem

Every injective real sequence of length `(r - 1) * (s - 1) + 1` contains an
increasing subsequence of length `r` or a decreasing subsequence of length `s`.

Source: P. Erdős and G. Szekeres, “A combinatorial problem in geometry,”
_Compositio Mathematica_ 2 (1935), 463–470; the two-parameter
monotone-subsequence bound is proved on p. 468.
NUMDAM record: https://www.numdam.org/item/CM_1935__2__463_0/.
-/

/-- `k - 1 < k` for positive `k`. -/
theorem sub_one_lt_of_pos {k : ℕ} (hk : 0 < k) : k - 1 < k := by omega

/-- An increasing subsequence of `f` of length `k`: index- and value-strict. -/
def IsIncrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ i) < f (φ j))

/-- A decreasing subsequence of `f` of length `k`: index-strict, values strictly
decrease. -/
def IsDecrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ j) < f (φ i))

/-- There is an increasing subsequence of length `k` ending exactly at `p`. -/
def IsIncrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsIncrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- There is a decreasing subsequence of length `k` ending exactly at `p`. -/
def IsDecrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsDecrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- Classical decidability for filtering positions by `IsIncrEnd`. -/
noncomputable instance decIncrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsIncrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- Classical decidability for filtering positions by `IsDecrEnd`. -/
noncomputable instance decDecrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsDecrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- No strict pair exists in `Fin 1`. -/
theorem fin1_false {i j : Fin 1} (hij : i < j) : False := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have h1 := i.isLt
  have h2 := j.isLt
  omega

/-- Singletons are increasing subsequences. -/
theorem singleton_incr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- Singletons are decreasing subsequences. -/
theorem singleton_decr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- Length of the longest increasing subsequence ending at `p`. -/
noncomputable def incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsIncrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_incr f p, rfl⟩⟩

/-- Length of the longest decreasing subsequence ending at `p`. -/
noncomputable def decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsDecrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_decr f p, rfl⟩⟩

/-- An index-strict map into `Fin N` has domain length at most `N`. -/
theorem subseqLen_le {N k : ℕ} {φ : Fin k → Fin N}
    (hidx : ∀ i j : Fin k, i < j → φ i < φ j) : k ≤ N := by
  have hinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    rcases lt_trichotomy i j with h | h | h
    · exact (ne_of_lt (hidx i j h)) hij
    · exact hne h
    · exact (ne_of_gt (hidx j i h)) hij
  have hcard := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at hcard
  exact hcard

/-- Witness for `incrLen`: a subsequence of that length ends at `p`. -/
theorem incrLen_isEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrEnd f p (incrLen f p) :=
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- Witness for `decrLen`: a subsequence of that length ends at `p`. -/
theorem decrLen_isEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrEnd f p (decrLen f p) :=
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- `incrLen` is an upper bound on lengths ending at `p`. -/
theorem le_incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ)
    (h : IsIncrEnd f p k) : k ≤ incrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsIncrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

/-- `decrLen` is an upper bound on lengths ending at `p`. -/
theorem le_decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ)
    (h : IsDecrEnd f p k) : k ≤ decrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsDecrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

/-- Lengths are positive. -/
theorem incrLen_ge_one {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    1 ≤ incrLen f p :=
  le_incrLen f p 1 ⟨by omega, fun _ => p, singleton_incr f p, rfl⟩

/-- Lengths are positive. -/
theorem decrLen_ge_one {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    1 ≤ decrLen f p :=
  le_decrLen f p 1 ⟨by omega, fun _ => p, singleton_decr f p, rfl⟩

/-- Append `p` to a length-`k` map, yielding a length-`k+1` map. -/
def extendMap {N k : ℕ} (φ : Fin k → Fin N) (p : Fin N) : Fin (k + 1) → Fin N :=
  fun i => if h : i.val < k then φ ⟨i.val, h⟩ else p

/-- Entries strictly before the end sit weakly below the end position. -/
theorem idx_le_last {N k : ℕ} {q : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    φ ⟨i.val, hik⟩ ≤ q := by
  have hval : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hidx _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

/-- Entries strictly before the end sit weakly below the end value along an
increasing subsequence. -/
theorem val_le_last_incr {N k : ℕ} {f : Fin N → ℝ} {q : Fin N}
    {φ : Fin k → Fin N} (hk : 0 < k)
    (hval : ∀ i j : Fin k, i < j → f (φ i) < f (φ j))
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    f (φ ⟨i.val, hik⟩) ≤ f q := by
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

/-- The end value sits weakly below later entries along a decreasing
subsequence. -/
theorem last_le_val_decr {N k : ℕ} {f : Fin N → ℝ} {q : Fin N}
    {φ : Fin k → Fin N} (hk : 0 < k)
    (hval : ∀ i j : Fin k, i < j → f (φ j) < f (φ i))
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    f q ≤ f (φ ⟨i.val, hik⟩) := by
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, ← hlast]

/-- The appended map is index-strict. -/
theorem extend_idx {N k : ℕ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q) (hqp : q < p)
    (i j : Fin (k + 1)) (hij : i < j) :
    extendMap φ p i < extendMap φ p j := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have hik : i.val < k := by omega
  change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
    (if h : j.val < k then φ ⟨j.val, h⟩ else p)
  by_cases hjk : j.val < k
  · rw [dite_eq_left hik, dite_eq_left hjk]
    exact hidx _ _ (Fin.lt_def.mpr hiv)
  · rw [dite_eq_left hik, dite_eq_right hjk]
    exact lt_of_le_of_lt (idx_le_last hk hidx hlast hik) hqp

/-- The last element of the appended map is `p`. -/
theorem extend_last {N k : ℕ} (φ : Fin k → Fin N) {p : Fin N}
    (hk1 : 0 < k + 1) :
    extendMap φ p ⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ = p := by
  have hval : (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val =
      k + 1 - 1 := rfl
  have hneg : ¬ (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val < k := by
    omega
  unfold extendMap
  exact dite_eq_right hneg

/-- Extend an increasing subsequence ending at `q` by appending `p` after it. -/
theorem incrExtend {N k : ℕ} {f : Fin N → ℝ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hsub : IsIncrSubseq f k φ)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    (hqp : q < p) (hval : f q < f p) : IsIncrEnd f p (k + 1) := by
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.1 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (idx_le_last hk hsub.1 hlast hik) hqp
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      f (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (val_le_last_incr hk hsub.2 hlast hik) hval

/-- Extend a decreasing subsequence ending at `q` by appending `p` after it. -/
theorem decrExtend {N k : ℕ} {f : Fin N → ℝ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hsub : IsDecrSubseq f k φ)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    (hqp : q < p) (hval : f p < f q) : IsDecrEnd f p (k + 1) := by
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    exact extend_idx hk hsub.1 hlast hqp i j hij
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : j.val < k then φ ⟨j.val, h⟩ else p) <
      f (if h : i.val < k then φ ⟨i.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_lt_of_le hval (last_le_val_decr hk hsub.2 hlast hik)

/-- `incrLen` grows along index- and value-increases. -/
theorem incrMono {N : ℕ} (f : Fin N → ℝ) {q p : Fin N}
    (hqp : q < p) (hval : f q < f p) : incrLen f q < incrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := incrLen_isEnd f q
  have hle : incrLen f q + 1 ≤ incrLen f p :=
    le_incrLen f p _ (incrExtend hk hsub hlast hqp hval)
  omega

/-- `decrLen` grows along index-increases and value-decreases. -/
theorem decrMono {N : ℕ} (f : Fin N → ℝ) {q p : Fin N}
    (hqp : q < p) (hval : f p < f q) : decrLen f q < decrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := decrLen_isEnd f q
  have hle : decrLen f q + 1 ≤ decrLen f p :=
    le_decrLen f p _ (decrExtend hk hsub hlast hqp hval)
  omega

/-- An increasing subsequence truncates to any shorter length. -/
theorem truncIncr {N k r : ℕ} {f : Fin N → ℝ} {φ : Fin k → Fin N}
    (hsub : IsIncrSubseq f k φ) (hrk : r ≤ k) :
    ∃ φ' : Fin r → Fin N, IsIncrSubseq f r φ' :=
  ⟨fun i => φ (Fin.castLE hrk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

/-- A decreasing subsequence truncates to any shorter length. -/
theorem truncDecr {N k s : ℕ} {f : Fin N → ℝ} {φ : Fin k → Fin N}
    (hsub : IsDecrSubseq f k φ) (hsk : s ≤ k) :
    ∃ ψ : Fin s → Fin N, IsDecrSubseq f s ψ :=
  ⟨fun i => φ (Fin.castLE hsk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

/-- **Erdős–Szekeres**: every injective real sequence of length
`(r - 1) * (s - 1) + 1` contains an increasing subsequence of length `r` or a
decreasing subsequence of length `s`. -/
public theorem erdos_szekeres {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ) (hinj : Function.Injective f) :
    (∃ φ : Fin r → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin r, i < j → φ i < φ j) ∧
      (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) := by
  classical
  by_cases hr1 : r = 1
  · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
    subst hr1
    refine Or.inl ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
      exact False.elim (fin1_false hij)
  · by_cases hs1 : s = 1
    · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
      subst hs1
      refine Or.inr ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
        exact False.elim (fin1_false hij)
    · have hr2 : 1 < r := by omega
      have hs2 : 1 < s := by omega
      by_cases ha : ∃ p, r ≤ incrLen f p
      · obtain ⟨p, hp⟩ := ha
        obtain ⟨_, φ, hsub, _⟩ := incrLen_isEnd f p
        obtain ⟨φ', hsub'⟩ := truncIncr hsub hp
        exact Or.inl ⟨φ', hsub'.1, hsub'.2⟩
      · by_cases hb : ∃ p, s ≤ decrLen f p
        · obtain ⟨p, hp⟩ := hb
          obtain ⟨_, φ, hsub, _⟩ := decrLen_isEnd f p
          obtain ⟨ψ, hsub'⟩ := truncDecr hsub hp
          exact Or.inr ⟨ψ, hsub'.1, hsub'.2⟩
        · have ha' : ∀ p, incrLen f p < r :=
            fun p => not_le.mp (fun h => ha ⟨p, h⟩)
          have hb' : ∀ p, decrLen f p < s :=
            fun p => not_le.mp (fun h => hb ⟨p, h⟩)
          have hmem1 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
              incrLen f p - 1 < r - 1 := by
            intro p
            have h1 := incrLen_ge_one f p
            have h2 := ha' p
            omega
          have hmem2 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
              decrLen f p - 1 < s - 1 := by
            intro p
            have h1 := decrLen_ge_one f p
            have h2 := hb' p
            omega
          have hcard :
              (Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))).card <
              (Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1))).card := by
            rw [Finset.card_univ, Finset.card_univ, Fintype.card_prod,
              Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
            exact Nat.lt_succ_self _
          have hmap : Set.MapsTo
              (fun p : Fin ((r - 1) * (s - 1) + 1) =>
                ((⟨incrLen f p - 1, hmem1 p⟩ : Fin (r - 1)),
                  (⟨decrLen f p - 1, hmem2 p⟩ : Fin (s - 1))))
              ↑(Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1)))
              ↑(Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))) := by
            intro x _
            exact Finset.mem_univ _
          obtain ⟨x, _, y, _, hne, heq⟩ :=
            Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap
          have ha_mk : (⟨incrLen f x - 1, hmem1 x⟩ : Fin (r - 1)) =
              ⟨incrLen f y - 1, hmem1 y⟩ :=
            congrArg Prod.fst heq
          have hb_mk : (⟨decrLen f x - 1, hmem2 x⟩ : Fin (s - 1)) =
              ⟨decrLen f y - 1, hmem2 y⟩ :=
            congrArg Prod.snd heq
          have ha_sub : incrLen f x - 1 = incrLen f y - 1 :=
            Fin.ext_iff.mp ha_mk
          have hb_sub : decrLen f x - 1 = decrLen f y - 1 :=
            Fin.ext_iff.mp hb_mk
          have ha_eq : incrLen f x = incrLen f y := by
            have h1 := incrLen_ge_one f x
            have h2 := incrLen_ge_one f y
            omega
          have hb_eq : decrLen f x = decrLen f y := by
            have h1 := decrLen_ge_one f x
            have h2 := decrLen_ge_one f y
            omega
          have hval_ne : x.val ≠ y.val := fun h => hne (Fin.ext_iff.mpr h)
          rcases lt_trichotomy x.val y.val with hlt | heq_val | hgt
          · have hxy : x < y := Fin.lt_def.mpr hlt
            have hfne : f x ≠ f y := fun h => hne (hinj h)
            rcases lt_trichotomy (f x) (f y) with hltf | heqf | hgtf
            · exfalso
              have hm := incrMono f hxy hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hxy hgtf
              omega
          · exact absurd heq_val hval_ne
          · have hyx : y < x := Fin.lt_def.mpr hgt
            have hfne : f y ≠ f x := fun h => hne (hinj h).symm
            rcases lt_trichotomy (f y) (f x) with hltf | heqf | hgtf
            · exfalso
              have hm := incrMono f hyx hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hyx hgtf
              omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres
