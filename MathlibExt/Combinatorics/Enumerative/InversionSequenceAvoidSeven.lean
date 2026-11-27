/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternSets
import all MathlibExt.Combinatorics.Enumerative.InversionSequenceAvoid011102120
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# A common generating function for three sets of seven inversion-sequence patterns

For each of the sets `{010, 011, 100, 101, 102, 201, 210}`, `{010, 011, 100, 102, 110, 201, 210}`
and `{010, 011, 101, 102, 110, 201, 210}`, the positive-length avoidance generating function is
`x / (1 - x) + x² (1 - x) / (1 - 2x)²`. The three sets have the same avoiders: zeros come first,
positive values are distinct, and the positive entries before the final position are increasing.
We count them by the last entry and the set of positive values in the prefix.

## References

* Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024),
  Article A76, pp. 1–112, Theorem 16 (pp. 78–79).
* David Callan and Toufik Mansour, *Inversion Sequences Avoiding Quadruple Length-3 Patterns*,
  INTEGERS 23 (2023), Article A78, pp. 1–64, Theorems 2 and 3 (pp. 3–4), for the reductions
  involving `100`, `101` and `110` also recorded in Mansour's Theorem 2.
* `MathlibExt.Combinatorics.Enumerative.InversionSequenceAvoid011102120`: the proof reuses
  `invSeqAvoidGF_011_102_120.contains_iff` and `invSeqAvoidGF_011_102_120.SameOrder` to translate
  pattern avoidance into comparisons of entries.
-/

namespace MetaMathlibExt

open Finset PowerSeries

namespace InversionSequenceAvoidSeven

open invSeqAvoidGF_011_102_120 (contains_iff SameOrder)

private def corePatterns : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]}

private def allPatterns : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}

/-- A positive entry is followed by distinct positive entries, and a descent may end only at
 the last position. -/
private def Shape {n : ℕ} (e : Fin n → ℕ) : Prop :=
  ∀ ⦃i j⦄, i < j → 0 < e i → 0 < e j ∧ e i ≠ e j ∧ ((j : ℕ) + 1 < n → e i < e j)

private theorem shape_iff {n : ℕ} {e : Fin n → ℕ} {B : Set (Fin 3 → ℕ)}
    (hb : ∀ i, e i ≤ i) (hcore : corePatterns ⊆ B) (hall : B ⊆ allPatterns) :
    (∀ p ∈ B, ¬ InvSeqContainsPattern e p) ↔ Shape e := by
  constructor
  · intro h
    have ht {i j k : Fin n} (hij : i < j) (hjk : j < k) (p : Fin 3 → ℕ)
        (hp : p ∈ corePatterns) : ¬ SameOrder (e i) (e j) (e k) p := fun hs =>
      h p (hcore hp) ((contains_iff e p).mpr ⟨i, j, k, hij, hjk, hs⟩)
    have hpos {i j : Fin n} (hij : i < j) (hi : 0 < e i) : 0 < e j ∧ e i ≠ e j := by
      let z : Fin n := ⟨0, by omega⟩
      have hz : e z = 0 := Nat.eq_zero_of_le_zero (hb z)
      have hzi : z < i := by
        have := hb i
        change 0 < i.val
        omega
      have h010 := ht hzi hij ![0, 1, 0] (by simp [corePatterns])
      have h011 := ht hzi hij ![0, 1, 1] (by simp [corePatterns])
      simp [SameOrder, Fin.forall_fin_succ, hz] at h010 h011
      omega
    intro i j hij hi
    obtain ⟨hj, hne⟩ := hpos hij hi
    refine ⟨hj, hne, fun hnext => ?_⟩
    let k : Fin n := ⟨j.val + 1, hnext⟩
    have hjk : j < k := Nat.lt_succ_self _
    have hik := (hpos (hij.trans hjk) hi).2
    have hjk' := (hpos hjk hj).2
    have h102 := ht hij hjk ![1, 0, 2] (by simp [corePatterns])
    have h201 := ht hij hjk ![2, 0, 1] (by simp [corePatterns])
    have h210 := ht hij hjk ![2, 1, 0] (by simp [corePatterns])
    simp [SameOrder, Fin.forall_fin_succ] at h102 h201 h210
    omega
  · intro h p hp hc
    obtain ⟨i, j, k, hij, hjk, hs⟩ := (contains_iff e p).mp hc
    have hbefore : j.val + 1 < n := by omega
    have hij' := h hij
    have hik' := h (hij.trans hjk)
    have hjk' := h hjk
    have hp' := hall hp
    simp only [allPatterns, Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SameOrder, Fin.forall_fin_succ] at hs <;> omega

private def positiveValues {k : ℕ} (e : Fin k → ℕ) : Finset ℕ :=
  (univ.filter fun i => 0 < e i).image e

private theorem mem_positiveValues {k : ℕ} {e : Fin k → ℕ} {x : ℕ} :
    x ∈ positiveValues e ↔ ∃ i, 0 < e i ∧ e i = x := by
  simp [positiveValues]

-- Reading from the right, any larger value at the current position would have to occur
-- strictly to the right in the other prefix, where the two prefixes already agree.
private theorem prefix_eq_of_positiveValues {k : ℕ} {e f : Fin k → ℕ}
    (he : ∀ ⦃i j⦄, i < j → 0 < e i → e i < e j)
    (hf : ∀ ⦃i j⦄, i < j → 0 < f i → f i < f j)
    (hs : positiveValues e = positiveValues f) : e = f := by
  have leAt {u v : Fin k → ℕ} {i : Fin k}
      (hu : ∀ ⦃a b⦄, a < b → 0 < u a → u a < u b)
      (hv : ∀ ⦃a b⦄, a < b → 0 < v a → v a < v b)
      (hs' : positiveValues u = positiveValues v) (hr : ∀ j, i < j → u j = v j) :
      v i ≤ u i := by
    by_contra! h
    have hp : 0 < v i := Nat.zero_lt_of_lt h
    have hm : v i ∈ positiveValues u :=
      hs'.symm ▸ mem_positiveValues.mpr ⟨i, hp, rfl⟩
    obtain ⟨j, hj, heq⟩ := mem_positiveValues.mp hm
    have hij : i < j := by
      rcases lt_trichotomy j i with hji | rfl | hij
      · have := hu hji hj
        omega
      · omega
      · exact hij
    have := hv hij hp
    rw [← hr j hij, heq] at this
    exact (lt_irrefl _ this)
  funext i
  refine (measure (fun j : Fin k => k - j.val)).wf.induction (C := fun j => e j = f j)
    i fun i ih => ?_
  have hr (j : Fin k) (hij : i < j) : e j = f j := by
    apply ih j
    change k - j.val < k - i.val
    omega
  exact le_antisymm (leAt hf he hs.symm fun j hj => (hr j hj).symm) (leAt he hf hs hr)

-- Right-align the increasingly enumerated set. The values from rank `r` onward all lie in
-- `[value r, m]`, so the interval has room for at least `s.card - r` values.
private theorem exists_prefix {m : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc 1 m) :
    ∃ e : Fin (m + 1) → ℕ,
      (∀ i, e i ≤ i) ∧ (∀ ⦃i j⦄, i < j → 0 < e i → e i < e j) ∧ positiveValues e = s := by
  have hcard : s.card ≤ m := by simpa using card_le_card hs
  let pad := m + 1 - s.card
  let rank (i : Fin (m + 1)) (hi : pad ≤ i.val) : Fin s.card := ⟨i.val - pad, by
    dsimp [pad] at hi ⊢
    omega⟩
  let value := s.orderEmbOfFin rfl
  let e (i : Fin (m + 1)) : ℕ := if hi : pad ≤ i.val then value (rank i hi) else 0
  have hvalue (r : Fin s.card) : value r ∈ Icc 1 m := hs (s.orderEmbOfFin_mem rfl r)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    dsimp only [e]
    split_ifs with hi
    · let r := rank i hi
      change value r ≤ i.val
      have hsub : (Ici r).map value.toEmbedding ⊆ Icc (value r) m := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := mem_map.mp hx
        exact mem_Icc.mpr ⟨value.monotone (mem_Ici.mp hj), (mem_Icc.mp (hvalue j)).2⟩
      have hc := card_le_card hsub
      rw [card_map, Fin.card_Ici, Nat.card_Icc] at hc
      have hr : r.val = i.val - pad := rfl
      have hrv := r.isLt
      dsimp [pad] at hr hi
      omega
    · exact Nat.zero_le _
  · intro i j hij hi
    have hpi : pad ≤ i.val := by
      by_contra! h
      simp [e, not_le_of_gt h] at hi
    have hpj : pad ≤ j.val := le_trans hpi hij.le
    simp only [e, dite_eq_left hpi, dite_eq_left hpj]
    apply value.strictMono
    change i.val - pad < j.val - pad
    omega
  · ext x
    rw [mem_positiveValues]
    constructor
    · rintro ⟨i, hi, rfl⟩
      dsimp only [e] at hi ⊢
      split_ifs at hi ⊢
      · exact s.orderEmbOfFin_mem rfl _
      · exact False.elim (Nat.lt_irrefl _ hi)
    · intro hx
      have hrs : x ∈ Set.range value := by simpa [value, range_orderEmbOfFin] using hx
      obtain ⟨r, rfl⟩ := hrs
      let i : Fin (m + 1) := ⟨r.val + pad, by dsimp [pad]; omega⟩
      have hi : pad ≤ i.val := Nat.le_add_left _ _
      have hr : rank i hi = r := Fin.ext (Nat.add_sub_cancel _ _)
      refine ⟨i, ?_, by simp [e, hi, hr]⟩
      have : 0 < value r := (mem_Icc.mp (hvalue r)).1
      simpa [e, hi, hr] using this

private abbrev Shaped (m : ℕ) := {e : Fin (m + 2) → ℕ // (∀ i, e i ≤ i) ∧ Shape e}

private def lastValue {m : ℕ} (e : Shaped m) : Fin (m + 2) :=
  ⟨e.1 (Fin.last (m + 1)), Nat.lt_succ_of_le (e.2.1 _)⟩

private def choices (m : ℕ) (a : Fin (m + 2)) : Finset ℕ :=
  if a.val = 0 then ∅ else (Icc 1 m).erase a.val

-- With the final value fixed, only its compatible subset of positive prefix values is free.
private noncomputable def choicesEquiv {m : ℕ} (a : Fin (m + 2)) :
    {e : Shaped m // lastValue e = a} ≃ ↥(choices m a).powerset := by
  have increasing (e : Shaped m) {i j : Fin (m + 1)} (hij : i < j)
      (hi : 0 < Fin.init e.1 i) : Fin.init e.1 i < Fin.init e.1 j :=
    (e.2.2 (i := i.castSucc) (j := j.castSucc) hij hi).2.2 (by simp; omega)
  let encode (e : {e : Shaped m // lastValue e = a}) : ↥(choices m a).powerset :=
    ⟨positiveValues (Fin.init e.1.1), mem_powerset.mpr (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_positiveValues.mp hx
      have hlast : e.1.1 (Fin.last (m + 1)) = a.val := congrArg Fin.val e.2
      obtain ⟨hpos, hne, _⟩ := e.1.2.2 (Fin.castSucc_lt_last i) hi
      rw [hlast] at hpos hne
      simp only [choices, ite_eq_right (Nat.ne_of_gt hpos), mem_erase, mem_Icc]
      exact ⟨hne, hi, (e.1.2.1 i.castSucc).trans (Nat.le_of_lt_succ i.isLt)⟩)⟩
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · intro e f hef
    have heq : Fin.init e.1.1 = Fin.init f.1.1 :=
      prefix_eq_of_positiveValues (fun _ _ => increasing e.1) (fun _ _ => increasing f.1)
        (congrArg Subtype.val hef)
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => congrFun heq j) i
    exact congrArg Fin.val (e.2.trans f.2.symm)
  · intro s
    have hsub := mem_powerset.mp s.2
    have hchoices : choices m a ⊆ Icc 1 m := by
      unfold choices
      split_ifs
      · exact empty_subset _
      · exact erase_subset _ _
    obtain ⟨p, hpb, hpi, hps⟩ := exists_prefix (hsub.trans hchoices)
    let e : Fin (m + 2) → ℕ := Fin.snoc p a.val
    have heb (i : Fin (m + 2)) : e i ≤ i := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [e] using Nat.le_of_lt_succ a.isLt
      · simpa [e] using hpb j
    have hes : Shape e := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j hij
        exact (not_lt_of_ge (Fin.le_last j) hij).elim
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _ hi
          have hp : 0 < p i := by simpa [e] using hi
          have hmem : p i ∈ choices m a := hsub (hps ▸ mem_positiveValues.mpr ⟨i, hp, rfl⟩)
          have ha : a.val ≠ 0 := by
            intro ha
            simp [choices, ha] at hmem
          simp only [choices, ite_eq_right ha, mem_erase] at hmem
          simpa [e] using ⟨Nat.pos_of_ne_zero ha, hmem.1⟩
        · intro hij hi
          have hp := hpi (show i < j from hij) (show 0 < p i from by simpa [e] using hi)
          simpa [e] using ⟨Nat.zero_lt_of_lt hp, hp.ne, fun _ => hp⟩
    have hlast : lastValue (⟨e, heb, hes⟩ : Shaped m) = a := by
      apply Fin.ext
      simp [lastValue, e]
    refine ⟨⟨⟨e, heb, hes⟩, hlast⟩, Subtype.ext ?_⟩
    simpa [encode, e] using hps

private theorem count_eq_sum {B : Set (Fin 3 → ℕ)} (hcore : corePatterns ⊆ B)
    (hall : B ⊆ allPatterns) (m : ℕ) :
    invSeqAvoidCount B (m + 2) = ∑ a : Fin (m + 2), 2 ^ (choices m a).card := by
  have e : {e : Fin (m + 2) → ℕ // (∀ i, e i ≤ i) ∧ ∀ p ∈ B, ¬ InvSeqContainsPattern e p} ≃
      Shaped m := Equiv.subtypeEquivRight fun e => and_congr_right fun hb => shape_iff hb hcore hall
  rw [invSeqAvoidCount, Nat.card_congr e,
    Nat.card_congr ((Equiv.sigmaFiberEquiv lastValue).symm.trans
      (Equiv.sigmaCongrRight choicesEquiv)), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, card_powerset]

-- There is one all-zero sequence. A maximal last value leaves all `m` candidates
-- available, and each of the `m` other positive last values deletes one candidate.
private theorem count_add_two {B : Set (Fin 3 → ℕ)} (hcore : corePatterns ⊆ B)
    (hall : B ⊆ allPatterns) (m : ℕ) :
    invSeqAvoidCount B (m + 2) = 1 + m * 2 ^ (m - 1) + 2 ^ m := by
  rw [count_eq_sum hcore hall, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hzero : (choices m (0 : Fin (m + 1)).castSucc).card = 0 := by simp [choices]
  have hlast : (choices m (Fin.last (m + 1))).card = m := by simp [choices]
  have hmid (i : Fin m) : (choices m i.succ.castSucc).card = m - 1 := by
    have hm : i.val + 1 ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, i.isLt⟩
    simp [choices, card_erase_of_mem hm]
  rw [hzero, hlast]
  simp_rw [hmid]
  simp

private theorem gf_eq {B : Set (Fin 3 → ℕ)} (hcore : corePatterns ⊆ B)
    (hall : B ⊆ allPatterns) :
    (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B = X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2 := by
  let A : ℚ⟦X⟧ := (invOneSubPow ℚ 1).val
  let H : ℚ⟦X⟧ := rescale 2 (invOneSubPow ℚ 2).val
  have hA : (1 - X) * A = 1 := by
    simpa [A] using one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ 0 1
  have hH : (1 - 2 * X) ^ 2 * H = 1 := by
    have h := congrArg (rescale (2 : ℚ))
      (one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ 0 2)
    simpa [H, rescale_X, map_ofNat] using h
  have cA (n : ℕ) : coeff n A = 1 := by
    simp [A, invOneSubPow_val_succ_eq_mk_add_choose]
  have cH (n : ℕ) : coeff n H = (n + 1 : ℚ) * 2 ^ n := by
    simp [H, invOneSubPow_val_succ_eq_mk_add_choose, Nat.add_comm, mul_comm]
  have h0 := (coeff_invSeqAvoidGF B 0).1
  have h1 : coeff 1 (invSeqAvoidGF B) = 1 := by
    rw [(coeff_invSeqAvoidGF B 0).2, invSeqAvoidCount_one, Nat.cast_one]
  have h2 : coeff 2 (invSeqAvoidGF B) = 2 := by
    rw [(coeff_invSeqAvoidGF B 1).2, count_add_two hcore hall 0]
    norm_num
  have h3 (m : ℕ) : coeff (m + 3) (invSeqAvoidGF B) = 1 + (m + 3 : ℚ) * 2 ^ m := by
    rw [(coeff_invSeqAvoidGF B (m + 2)).2, count_add_two hcore hall (m + 1)]
    push_cast
    simp only [pow_succ]
    ring
  have hF : invSeqAvoidGF B = X ^ 1 * A + X ^ 2 * H - X ^ 3 * H := by
    ext n
    simp only [map_add, map_sub, coeff_X_pow_mul']
    rcases n with _ | _ | _ | m
    · norm_num [h0]
    · norm_num [h1, cA]
    · norm_num [h2, cA, cH]
    · change coeff (m + 3) (invSeqAvoidGF B) = _
      rw [h3]
      have hshift : m + 3 - 2 = m + 1 := by omega
      simp [cA, cH, hshift, pow_succ]
      ring
  rw [hF]
  calc
    _ = X * (1 - 2 * X) ^ 2 * ((1 - X) * A) +
        X ^ 2 * (1 - X) ^ 2 * ((1 - 2 * X) ^ 2 * H) := by ring
    _ = _ := by rw [hA, hH, mul_one, mul_one]

end InversionSequenceAvoidSeven

open InversionSequenceAvoidSeven in
/-- **A common generating function for three sets of seven patterns.** Let
$B_1 = \{010, 011, 100, 101, 102, 201, 210\}$, $B_2 = \{010, 011, 100, 102, 110, 201, 210\}$ and
$B_3 = \{010, 011, 101, 102, 110, 201, 210\}$, where a pattern is written as a digit string ($101$
is the triple $(1, 0, 1)$). For a set $B$ of patterns let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. Then for each $j \in \{1, 2, 3\}$,
$$(1 - x)(1 - 2x)^2 F_{B_j}(x) = x(1 - 2x)^2 + x^2(1 - x)^2.$$

Since $(1 - x)(1 - 2x)^2$ is a unit in $\mathbb{Q}[[x]]$, this says
$F_{B_j}(x) = x/(1 - x) + x^2(1 - x)/(1 - 2x)^2$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 16 (`integers-2024-A76-thm-16`). -/
public theorem invSeqAvoidGF_010_011_102_201_210_seven :
    ∀ B : Set (Fin 3 → ℕ),
      (B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]} ∨
        B = {![0, 1, 0], ![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}) →
      (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B =
        X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2 := by
  intro B hB
  have h : corePatterns ⊆ B ∧ B ⊆ allPatterns := by
    rcases hB with rfl | rfl | rfl <;> simp [corePatterns, allPatterns, Set.insert_subset_iff]
  exact gf_eq h.1 h.2

end MetaMathlibExt
