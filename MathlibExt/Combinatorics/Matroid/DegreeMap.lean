/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matroid.ChowRing
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LinearCombination

/-!
# The degree map of a matroid

A finite loopless matroid of rank `r + 1` has a unique degree map on its real Chow ring.
The proof starts with the constant weight on maximal flags. The intermediate flats in
each rank-two interval partition the difference of its endpoints, giving the balancing
identity. Intersecting a balanced weight with a variable gives a balanced weight on shorter
flags. These operations commute and satisfy the Chow relations, so evaluation at the empty
flag gives the degree map. Any degree map induces the same weights by evaluation on flag
monomials and obeys the same intersection formula.
-/

noncomputable section

open MvPolynomial MathlibExt.Combinatorics.Matroid.Chow
open scoped BigOperators

namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted

section

variable {α : Type*} (M : _root_.Matroid α)

private local instance properDecidableEq : DecidableEq (ProperFlat M) := Classical.decEq _

private instance properFintype [M.Finite] : Fintype (ProperFlat M) := Fintype.ofFinite _

private abbrev Chain (S : Finset (ProperFlat M)) : Prop :=
  ∀ F ∈ S, ∀ G ∈ S, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1

private theorem chain_mono {S T : Finset (ProperFlat M)} (hS : Chain M S) (h : T ⊆ S) :
    Chain M T := fun F hF G hG => hS F (h hF) G (h hG)

private theorem chain_insert {S : Finset (ProperFlat M)} {F : ProperFlat M}
    (hS : Chain M S) (hF : ∀ G ∈ S, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1) :
    Chain M (insert F S) := by
  intro G hG H hH
  simp only [Finset.mem_insert] at hG hH
  rcases hG with rfl | hG
  · rcases hH with rfl | hH
    · exact Or.inl (fun _ h => h)
    · exact hF _ hH
  · rcases hH with rfl | hH
    · exact (hF _ hG).symm
    · exact hS _ hG _ hH

section Rank

variable [M.Finite]

private def rank (F : Set α) : ℕ := (M.eRk F).toNat

private theorem rank_mono {F G : Set α} (h : F ⊆ G) : rank M F ≤ rank M G :=
  ENat.toNat_le_toNat (M.eRk_mono h) (M.isRkFinite_set G).eRk_lt_top.ne

private theorem rank_lt {F G : Set α} (hF : M.IsFlat F) (hG : M.IsFlat G)
    (h : F ⊂ G) : rank M F < rank M G := by
  by_contra! hn
  apply h.ne
  rw [← hF.closure, ← hG.closure]
  apply (M.isRkFinite_set F).closure_eq_closure_of_subset_of_eRk_ge_eRk h.le
  simpa [rank, ENat.natCast_toNat, (M.isRkFinite_set _).eRk_lt_top.ne] using
    (show ((rank M G : ℕ) : ℕ∞) ≤ (rank M F : ℕ) from by exact_mod_cast hn)

omit [M.Finite] in
private theorem rank_empty : rank M ∅ = 0 := by simp [rank]

omit [M.Finite] in
private theorem rank_ground {r : ℕ} (hr : M.eRank = r + 1) : rank M M.E = r + 1 := by
  simp [rank, hr, ENat.toNat_add]

private theorem rank_closure_insert {P : Set α} (hP : M.IsFlat P) {i : α}
    (hi : i ∈ M.E) (hiP : i ∉ P) : rank M (M.closure (insert i P)) = rank M P + 1 := by
  have h : i ∈ M.E \ M.closure P := ⟨hi, hP.closure.symm ▸ hiP⟩
  simp [rank, M.eRk_closure_eq, M.eRk_insert_eq_add_one h, ENat.toNat_add,
    (M.isRkFinite_set P).eRk_lt_top.ne]

variable [M.Loopless]

omit [M.Finite] in
private theorem empty_isFlat : M.IsFlat ∅ := by
  simpa [Matroid.closure_empty] using M.isFlat_closure ∅

private theorem rank_bounds {r : ℕ} (hr : M.eRank = r + 1) (F : ProperFlat M) :
    rank M F.1 ∈ Finset.Icc 1 r := by
  have h₁ := rank_lt M (empty_isFlat M) F.2.1 (Set.empty_ssubset.mpr F.2.2.1)
  have h₂ := rank_lt M F.2.1 M.ground_isFlat
    (F.2.1.subset_ground.ssubset_of_ne F.2.2.2)
  rw [rank_empty] at h₁
  rw [rank_ground M hr] at h₂
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

omit [M.Loopless] in
private theorem le_of_rank_le {F G : ProperFlat M}
    (h : F.1 ⊆ G.1 ∨ G.1 ⊆ F.1) (hr : rank M F.1 ≤ rank M G.1) : F.1 ⊆ G.1 := by
  rcases h with h | h
  · exact h
  by_contra hn
  exact (rank_lt M G.2.1 F.2.1 (lt_of_le_not_ge h hn)).not_ge hr

omit [M.Loopless] in
private theorem rank_injOn {S : Finset (ProperFlat M)} (hS : Chain M S) :
    Set.InjOn (fun F : ProperFlat M => rank M F.1) S := by
  intro F hF G hG h
  exact Subtype.ext (Set.Subset.antisymm (le_of_rank_le M (hS _ hF _ hG) h.le)
    (le_of_rank_le M (hS _ hG _ hF) h.ge))

private theorem rank_image_eq {S : Finset (ProperFlat M)} {r : ℕ}
    (hr : M.eRank = r + 1) (hS : Chain M S) (hc : S.card = r) :
    S.image (fun F => rank M F.1) = Finset.Icc 1 r := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨F, _, rfl⟩ := Finset.mem_image.mp hn
    exact rank_bounds M hr F
  rw [Finset.card_image_of_injOn (rank_injOn M hS), hc, Nat.card_Icc]
  omega

omit [M.Loopless] in
private theorem exists_gap {S : Finset (ProperFlat M)} {F : ProperFlat M}
    (hF : F ∉ S) (hS : Chain M (insert F S)) :
    ∃ P Q : Set α, (P = ∅ ∨ ∃ G ∈ S, G.1 = P) ∧
      (Q = M.E ∨ ∃ G ∈ S, G.1 = Q) ∧
      P ⊂ F.1 ∧ F.1 ⊂ Q ∧ ∀ G ∈ S, G.1 ⊆ P ∨ Q ⊆ G.1 := by
  classical
  let L := S.filter fun G => G.1 ⊂ F.1
  let U := S.filter fun G => F.1 ⊂ G.1
  have lower : ∃ P : Set α, (P = ∅ ∨ ∃ G ∈ S, G.1 = P) ∧ P ⊂ F.1 ∧
      ∀ G ∈ L, G.1 ⊆ P := by
    by_cases hL : L.Nonempty
    · obtain ⟨A, hA, hmax⟩ := L.exists_max_image (fun G => rank M G.1) hL
      obtain ⟨hAS, hAF⟩ := Finset.mem_filter.mp hA
      refine ⟨A.1, Or.inr ⟨A, hAS, rfl⟩, hAF, fun G hG => ?_⟩
      exact le_of_rank_le M
        (hS _ (Finset.mem_insert_of_mem (Finset.mem_filter.mp hG).1) _
          (Finset.mem_insert_of_mem hAS)) (hmax G hG)
    · exact ⟨∅, Or.inl rfl, Set.empty_ssubset.mpr F.2.2.1, fun G hG => (hL ⟨G, hG⟩).elim⟩
  have upper : ∃ Q : Set α, (Q = M.E ∨ ∃ G ∈ S, G.1 = Q) ∧ F.1 ⊂ Q ∧
      ∀ G ∈ U, Q ⊆ G.1 := by
    by_cases hU : U.Nonempty
    · obtain ⟨A, hA, hmin⟩ := U.exists_min_image (fun G => rank M G.1) hU
      obtain ⟨hAS, hFA⟩ := Finset.mem_filter.mp hA
      refine ⟨A.1, Or.inr ⟨A, hAS, rfl⟩, hFA, fun G hG => ?_⟩
      exact le_of_rank_le M
        (hS _ (Finset.mem_insert_of_mem hAS) _
          (Finset.mem_insert_of_mem (Finset.mem_filter.mp hG).1)) (hmin G hG)
    · refine ⟨M.E, Or.inl rfl, F.2.1.subset_ground.ssubset_of_ne F.2.2.2, fun G hG => ?_⟩
      exact (hU ⟨G, hG⟩).elim
  obtain ⟨P, hP, hPF, hL⟩ := lower
  obtain ⟨Q, hQ, hFQ, hU⟩ := upper
  refine ⟨P, Q, hP, hQ, hPF, hFQ, fun G hG => ?_⟩
  have hn : G.1 ≠ F.1 := fun h => hF (Subtype.ext h ▸ hG)
  rcases hS G (Finset.mem_insert_of_mem hG) F (Finset.mem_insert_self _ _) with h | h
  · exact Or.inl (hL G (Finset.mem_filter.mpr ⟨hG, h.ssubset_of_ne hn⟩))
  · exact Or.inr (hU G (Finset.mem_filter.mpr ⟨hG, h.ssubset_of_ne hn.symm⟩))

end Rank

open Classical in
private def indicator (i : α) (F : Set α) : ℝ := if i ∈ F then 1 else 0

private def Forms : Submodule ℝ (Set α → ℝ) :=
  Submodule.span ℝ {f | ∃ i ∈ M.E, ∃ j ∈ M.E, f = indicator i - indicator j}

private theorem diff_mem_forms {i j : α} (hi : i ∈ M.E) (hj : j ∈ M.E) :
    indicator i - indicator j ∈ Forms M :=
  Submodule.subset_span ⟨i, hi, j, hj, rfl⟩

private theorem forms_endpoints (f : Forms M) : f.1 ∅ = 0 ∧ f.1 M.E = 0 := by
  obtain ⟨f, hf⟩ := f
  change f ∅ = 0 ∧ f M.E = 0
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, j, hj, rfl⟩ := hf
    simp [indicator, hi, hj]
  | zero => simp
  | add f g _ _ hf hg => simp [hf, hg]
  | smul a f _ hf => simp [hf]

section Interpolation

variable [M.Finite]

-- Differences of incidences in consecutive layers give the coordinate functions of a flag.
private theorem exists_coordinate {S : Finset (ProperFlat M)} (hS : Chain M S)
    {F : ProperFlat M} (hF : F ∈ S) :
    ∃ f : Forms M, ∀ G ∈ S, f.1 G.1 = if G = F then 1 else 0 := by
  have hins : insert F (S.erase F) = S := Finset.insert_erase hF
  obtain ⟨P, Q, _, hQ, hPF, hFQ, hgap⟩ := exists_gap M
    (Finset.notMem_erase F S) (hins.symm ▸ hS)
  obtain ⟨i, hiF, hiP⟩ := Set.exists_of_ssubset hPF
  obtain ⟨j, hjQ, hjF⟩ := Set.exists_of_ssubset hFQ
  have hQE : Q ⊆ M.E := by
    rcases hQ with rfl | ⟨H, _, rfl⟩
    · exact fun _ h => h
    · exact H.2.1.subset_ground
  refine ⟨⟨_, diff_mem_forms M (F.2.1.subset_ground hiF) (hQE hjQ)⟩, fun G hG => ?_⟩
  by_cases h : G = F
  · subst G
    simp [indicator, hiF, hjF]
  rcases hgap G (Finset.mem_erase.mpr ⟨h, hG⟩) with hn | hn
  · simp [h, indicator, show i ∉ G.1 from fun hi => hiP (hn hi),
      show j ∉ G.1 from fun hj => hjF (hPF.le (hn hj))]
  · simp [h, indicator, hn (hFQ.le hiF), hn hjQ]

private theorem exists_interpolant {S : Finset (ProperFlat M)} (hS : Chain M S)
    (u : ProperFlat M → ℝ) : ∃ f : Forms M, ∀ G ∈ S, f.1 G.1 = u G := by
  choose c hc using fun F : S => exists_coordinate M hS F.2
  refine ⟨∑ F : S, u F.1 • c F, fun G hG => ?_⟩
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hc _ _ hG]
  rw [Finset.sum_eq_single (⟨G, hG⟩ : S)]
  · simp
  · intro F _ hne
    have h : G ≠ F.1 := fun he => hne (Subtype.ext he.symm)
    simp [h]
  · simp

end Interpolation

section Intersection

variable [M.Finite]

private abbrev FlatFun := ProperFlat M → ℝ
private abbrev WeightFun := Finset (ProperFlat M) → ℝ

private def onFlats (f : Forms M) : FlatFun M := fun G => f.1 G.1

private def extend (w : WeightFun M) (S : Finset (ProperFlat M))
    (G : ProperFlat M) : ℝ := if G ∈ S then 0 else w (insert G S)

private def pair (w : WeightFun M) (S : Finset (ProperFlat M)) (u : FlatFun M) : ℝ :=
  ∑ G, extend M w S G * u G

private theorem pair_add (w : WeightFun M) (S : Finset (ProperFlat M)) (u v : FlatFun M) :
    pair M w S (u + v) = pair M w S u + pair M w S v := by
  simp [pair, mul_add, Finset.sum_add_distrib]

private theorem pair_sub (w : WeightFun M) (S : Finset (ProperFlat M)) (u v : FlatFun M) :
    pair M w S (u - v) = pair M w S u - pair M w S v := by
  simp [pair, mul_sub, Finset.sum_sub_distrib]

private theorem pair_smul (w : WeightFun M) (S : Finset (ProperFlat M))
    (a : ℝ) (u : FlatFun M) : pair M w S (a • u) = a * pair M w S u := by
  simp [pair, mul_left_comm, Finset.mul_sum]

private theorem pair_zero_of_not_chain {w : WeightFun M}
    (hw : ∀ S, ¬ Chain M S → w S = 0) {S : Finset (ProperFlat M)} (hS : ¬ Chain M S)
    (u : FlatFun M) : pair M w S u = 0 := by
  have h (G : ProperFlat M) : w (insert G S) = 0 :=
    hw _ (fun h => hS (chain_mono M h (Finset.subset_insert _ _)))
  simp [pair, extend, h]

private def Weights : Submodule ℝ (WeightFun M) where
  carrier := {w | (∀ S, ¬ Chain M S → w S = 0) ∧
    ∀ S (f : Forms M), (∀ G ∈ S, onFlats M f G = 0) → pair M w S (onFlats M f) = 0}
  zero_mem' := by simp [pair, extend]
  add_mem' := by
    rintro w v ⟨hw, hb⟩ ⟨hv, hc⟩
    refine ⟨fun S hS => by simp [hw S hS, hv S hS], fun S f hf => ?_⟩
    have h : ∀ G, extend M (w + v) S G = extend M w S G + extend M v S G := by
      intro G
      by_cases hG : G ∈ S <;> simp [extend, hG]
    calc
      pair M (w + v) S (onFlats M f) = pair M w S (onFlats M f) +
          pair M v S (onFlats M f) := by simp [pair, h, add_mul, Finset.sum_add_distrib]
      _ = 0 := by rw [hb S f hf, hc S f hf, add_zero]
  smul_mem' := by
    rintro a w ⟨hw, hb⟩
    refine ⟨fun S hS => by simp [hw S hS], fun S f hf => ?_⟩
    have h : ∀ G, extend M (a • w) S G = a * extend M w S G := by
      intro G
      by_cases hG : G ∈ S <;> simp [extend, hG]
    calc
      pair M (a • w) S (onFlats M f) = a * pair M w S (onFlats M f) := by
        simp only [pair, h, mul_assoc, Finset.mul_sum]
      _ = 0 := by rw [hb S f hf, mul_zero]

open Classical in
private def interpolant (S : Finset (ProperFlat M)) (u : FlatFun M) : Forms M :=
  if hS : Chain M S then (exists_interpolant M hS u).choose else 0

private theorem interpolant_eq {S : Finset (ProperFlat M)} (hS : Chain M S)
    (u : FlatFun M) {G : ProperFlat M} (hG : G ∈ S) :
    onFlats M (interpolant M S u) G = u G := by
  simpa only [interpolant, dite_eq_left hS, onFlats] using
    (exists_interpolant M hS u).choose_spec G hG

private def intersection (u : FlatFun M) (w : Weights M) : WeightFun M :=
  fun S => pair M w.1 S (u - onFlats M (interpolant M S u))

private theorem intersection_eq (u : FlatFun M) (w : Weights M)
    (S : Finset (ProperFlat M)) (f : Forms M) (hf : ∀ G ∈ S, onFlats M f G = u G) :
    intersection M u w S = pair M w.1 S (u - onFlats M f) := by
  by_cases hS : Chain M S
  · have he := w.2.2 S (interpolant M S u - f) (fun G hG => by
      change onFlats M (interpolant M S u) G - onFlats M f G = 0
      rw [interpolant_eq M hS u hG, hf G hG, sub_self])
    change pair M w.1 S (onFlats M (interpolant M S u) - onFlats M f) = 0 at he
    rw [pair_sub] at he
    simp only [intersection, pair_sub, sub_eq_zero.mp he]
  · unfold intersection
    rw [pair_zero_of_not_chain M w.2.1 hS, pair_zero_of_not_chain M w.2.1 hS]

private theorem intersection_sub_form (u : FlatFun M) (w : Weights M) (f : Forms M) :
    intersection M (u - onFlats M f) w = intersection M u w := by
  ext S
  by_cases hS : Chain M S
  · rw [intersection_eq M _ _ S (interpolant M S u - f) (fun G hG => by
      change onFlats M (interpolant M S u) G - onFlats M f G = _
      rw [interpolant_eq M hS u hG]
      rfl)]
    unfold intersection
    congr 1
    ext G
    change u G - onFlats M f G - (onFlats M (interpolant M S u) G - onFlats M f G) = _
    simp only [Pi.sub_apply]
    ring
  · exact (pair_zero_of_not_chain M w.2.1 hS _).trans
      (pair_zero_of_not_chain M w.2.1 hS _).symm

private theorem intersection_form (w : Weights M) (f : Forms M) :
    intersection M (onFlats M f) w = 0 := by
  ext S
  rw [intersection_eq M _ _ S f (fun _ _ => rfl), sub_self]
  simp [pair]

omit [M.Finite] in
private theorem extend_twice_symm (w : WeightFun M) (S : Finset (ProperFlat M))
    (F G : ProperFlat M) :
    extend M (fun T => extend M w T G) S F =
      extend M (fun T => extend M w T F) S G := by
  by_cases hFG : F = G
  · subst G
    rfl
  by_cases hF : F ∈ S <;> by_cases hG : G ∈ S <;>
    simp [extend, hFG, Ne.symm hFG, hF, hG, Finset.insert_comm F G]

-- With both functions zero on the fixed face, the two intersections can be swapped.
private theorem intersection_pair_symm (w : Weights M) (S : Finset (ProperFlat M))
    (u v : FlatFun M) (hu : ∀ G ∈ S, u G = 0) (hv : ∀ G ∈ S, v G = 0) :
    pair M (intersection M u w) S v = pair M (intersection M v w) S u := by
  let d (F G : ProperFlat M) := extend M (fun T => extend M w.1 T G) S F
  have hd (F G) : d F G = d G F := extend_twice_symm M _ _ _ _
  have step (F : ProperFlat M) :
      extend M (intersection M u w) S F * v F -
        extend M (intersection M v w) S F * u F =
      (∑ G, d F G * u G) * v F - (∑ G, d F G * v G) * u F := by
    by_cases hF : F ∈ S
    · simp [d, extend, hF]
    let T := insert F S
    simp only [d, extend, ite_eq_right hF]
    change intersection M u w T * v F - intersection M v w T * u F =
      pair M w.1 T u * v F - pair M w.1 T v * u F
    by_cases hT : Chain M T
    · let f := interpolant M T u
      let g := interpolant M T v
      have hf : ∀ G ∈ T, onFlats M f G = u G := fun _ hG => interpolant_eq M hT u hG
      have hg : ∀ G ∈ T, onFlats M g G = v G := fun _ hG => interpolant_eq M hT v hG
      have h := w.2.2 T (v F • f - u F • g) (fun G hG => by
        change v F * onFlats M f G - u F * onFlats M g G = 0
        rw [hf G hG, hg G hG]
        rcases Finset.mem_insert.mp hG with rfl | hG
        · ring
        · rw [hu G hG, hv G hG, mul_zero, mul_zero, sub_self])
      change pair M w.1 T (v F • onFlats M f - u F • onFlats M g) = 0 at h
      rw [pair_sub, pair_smul, pair_smul, sub_eq_zero] at h
      rw [intersection_eq M u w T f hf, intersection_eq M v w T g hg, pair_sub, pair_sub]
      linear_combination - h
    · simp only [intersection, pair_zero_of_not_chain M w.2.1 hT, zero_mul, sub_zero]
  have swap : (∑ F, ∑ G, d F G * u G * v F) = ∑ F, ∑ G, d F G * v G * u F := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun G _ => ?_
    rw [hd G F]
    ring
  rw [← sub_eq_zero]
  simp only [pair, ← Finset.sum_sub_distrib, step, Finset.sum_mul]
  simp only [Finset.sum_sub_distrib, swap, sub_self]

private def cap (u : FlatFun M) : Module.End ℝ (Weights M) where
  toFun w := ⟨intersection M u w, by
    refine ⟨fun S hS => pair_zero_of_not_chain M w.2.1 hS _, fun S f hf => ?_⟩
    by_cases hS : Chain M S
    · let g := interpolant M S u
      have hg : ∀ G ∈ S, (u - onFlats M g) G = 0 := fun G hG => by
        simp [g, interpolant_eq M hS u hG]
      rw [← intersection_sub_form M u w g, intersection_pair_symm M w S _ _ hg hf,
        intersection_form]
      simp [pair, extend]
    · exact pair_zero_of_not_chain M
        (fun T hT => pair_zero_of_not_chain M w.2.1 hT _) hS _⟩
  map_add' w v := by
    apply Subtype.ext
    funext S
    have h (G : ProperFlat M) :
        extend M (w.1 + v.1) S G = extend M w.1 S G + extend M v.1 S G := by
      by_cases hG : G ∈ S <;> simp [extend, hG]
    simp [intersection, pair, h, add_mul, Finset.sum_add_distrib]
  map_smul' a w := by
    apply Subtype.ext
    funext S
    have h (G : ProperFlat M) : extend M (a • w.1) S G = a * extend M w.1 S G := by
      by_cases hG : G ∈ S <;> simp [extend, hG]
    simp [intersection, pair, h, mul_assoc, Finset.mul_sum]

private theorem cap_commute (u v : FlatFun M) : Commute (cap M u) (cap M v) := by
  ext w S
  change intersection M u (cap M v w) S = intersection M v (cap M u w) S
  by_cases hS : Chain M S
  · let f := interpolant M S u
    let g := interpolant M S v
    have hf : ∀ G ∈ S, (u - onFlats M f) G = 0 := fun G hG => by
      simp [f, interpolant_eq M hS u hG]
    have hg : ∀ G ∈ S, (v - onFlats M g) G = 0 := fun G hG => by
      simp [g, interpolant_eq M hS v hG]
    change pair M (intersection M v w) S (u - onFlats M f) =
      pair M (intersection M u w) S (v - onFlats M g)
    rw [← intersection_sub_form M v w g, ← intersection_sub_form M u w f]
    exact intersection_pair_symm M w S _ _ hg hf
  · exact (pair_zero_of_not_chain M (cap M v w).2.1 hS _).trans
      (pair_zero_of_not_chain M (cap M u w).2.1 hS _).symm

private theorem cap_add (u v : FlatFun M) : cap M (u + v) = cap M u + cap M v := by
  ext w S
  change intersection M (u + v) w S = intersection M u w S + intersection M v w S
  by_cases hS : Chain M S
  · have h (t : FlatFun M) : ∀ G ∈ S, onFlats M (interpolant M S t) G = t G :=
      fun _ hG => interpolant_eq M hS t hG
    rw [intersection_eq M (u + v) w S (interpolant M S u + interpolant M S v) (fun G hG => by
      change onFlats M (interpolant M S u) G + onFlats M (interpolant M S v) G = _
      rw [h u G hG, h v G hG]
      rfl)]
    change pair M w.1 S ((u + v) - (onFlats M (interpolant M S u) +
      onFlats M (interpolant M S v))) = _
    rw [add_sub_add_comm, pair_add]
    rfl
  · simp only [intersection, pair_zero_of_not_chain M w.2.1 hS, add_zero]

private theorem cap_smul (a : ℝ) (u : FlatFun M) : cap M (a • u) = a • cap M u := by
  ext w S
  change intersection M (a • u) w S = a * intersection M u w S
  by_cases hS : Chain M S
  · rw [intersection_eq M (a • u) w S (a • interpolant M S u) (fun G hG => by
      change a * onFlats M (interpolant M S u) G = a * u G
      rw [interpolant_eq M hS u hG])]
    change pair M w.1 S (a • u - a • onFlats M (interpolant M S u)) = _
    rw [← smul_sub, pair_smul]
    rfl
  · simp only [intersection, pair_zero_of_not_chain M w.2.1 hS, mul_zero]

private def capLinear : FlatFun M →ₗ[ℝ] Module.End ℝ (Weights M) where
  toFun := cap M
  map_add' := cap_add M
  map_smul' := cap_smul M

private def delta (F : ProperFlat M) : FlatFun M := fun G => if G = F then 1 else 0

private theorem cap_delta_of_notMem (F : ProperFlat M) (w : Weights M)
    {S : Finset (ProperFlat M)} (hF : F ∉ S) :
    (cap M (delta M F) w).1 S = w.1 (insert F S) := by
  have h (G : ProperFlat M) (hG : G ∈ S) : G ≠ F := fun h => hF (h ▸ hG)
  change intersection M (delta M F) w S = _
  rw [intersection_eq M _ _ S 0 (fun G hG => by simp [onFlats, delta, h G hG])]
  simp [onFlats, pair, delta, extend, hF, mul_ite]

private theorem cap_delta_incomp {F G : ProperFlat M}
    (hFG : ¬ F.1 ⊆ G.1) (hGF : ¬ G.1 ⊆ F.1) :
    cap M (delta M F) * cap M (delta M G) = 0 := by
  have h (S : Finset (ProperFlat M)) (hF : F ∈ S) (hG : G ∈ S) : ¬ Chain M S :=
    fun hS => (hS F hF G hG).elim hFG hGF
  have hz (w : Weights M) (S : Finset (ProperFlat M)) (hF : F ∈ S) :
      (cap M (delta M G) w).1 S = 0 := by
    by_cases hG : G ∈ S
    · exact (cap M (delta M G) w).2.1 S (h S hF hG)
    · rw [cap_delta_of_notMem M G w hG]
      exact w.2.1 _ (h _ (Finset.mem_insert_of_mem hF) (Finset.mem_insert_self _ _))
  ext w S
  change (cap M (delta M F) (cap M (delta M G) w)).1 S = 0
  by_cases hF : F ∈ S
  · by_cases hG : G ∈ S
    · exact (cap M (delta M F) (cap M (delta M G) w)).2.1 S (h S hF hG)
    · have hc := congrArg (fun D : Module.End ℝ (Weights M) => (D w).1 S)
          (cap_commute M (delta M F) (delta M G)).eq
      change (cap M (delta M F) (cap M (delta M G) w)).1 S =
        (cap M (delta M G) (cap M (delta M F) w)).1 S at hc
      rw [hc, cap_delta_of_notMem M G _ hG]
      exact (cap M (delta M F) w).2.1 _
        (h (insert G S) (Finset.mem_insert_of_mem hF) (Finset.mem_insert_self _ _))
  · rw [cap_delta_of_notMem M F _ hF]
    exact hz w _ (Finset.mem_insert_self _ _)

end Intersection

section TopWeight

variable [M.Finite] [M.Loopless]

open Classical in
private def topFun (r : ℕ) : WeightFun M := fun S => if Chain M S ∧ S.card = r then 1 else 0

omit [M.Loopless] in
private theorem gap_partition {P Q : Set α} (hP : M.IsFlat P) (hQ : M.IsFlat Q)
    (hPQ : P ⊂ Q) (hr : rank M Q = rank M P + 2) {i : α} (hi : i ∈ Q \ P) :
    ∃ F : ProperFlat M, (P ⊂ F.1 ∧ F.1 ⊂ Q) ∧ i ∈ F.1 ∧
      ∀ G : ProperFlat M, (P ⊂ G.1 ∧ G.1 ⊂ Q) → i ∈ G.1 → G = F := by
  let A := M.closure (insert i P)
  have hA : M.IsFlat A := M.isFlat_closure _
  have hE : i ∈ M.E := hQ.subset_ground hi.1
  have hiA : i ∈ A := M.mem_closure_of_mem (Set.mem_insert _ _)
    (Set.insert_subset hE hP.subset_ground)
  have hPA : P ⊂ A := ((Set.subset_insert _ _).trans
    (M.subset_closure _ (Set.insert_subset hE hP.subset_ground))).ssubset_of_ne
      (fun h => hi.2 (h ▸ hiA))
  have hAr : rank M A = rank M P + 1 := rank_closure_insert M hP hE hi.2
  have hAQ : A ⊂ Q :=
    ((M.closure_subset_closure (Set.insert_subset hi.1 hPQ.le)).trans_eq hQ.closure).ssubset_of_ne
      (fun h => by change A = Q at h; rw [h, hr] at hAr; omega)
  let F : ProperFlat M := ⟨A, hA, ⟨i, hiA⟩, (hAQ.trans_le hQ.subset_ground).ne⟩
  refine ⟨F, ⟨hPA, hAQ⟩, hiA, fun G ⟨hPG, hGQ⟩ hiG => ?_⟩
  have hAG : A ⊆ G.1 :=
    (M.closure_subset_closure (Set.insert_subset hiG hPG.le)).trans_eq G.2.1.closure
  apply Subtype.ext
  by_contra hne
  have h₁ := rank_lt M hA G.2.1 (hAG.ssubset_of_ne (Ne.symm hne))
  have h₂ := rank_lt M G.2.1 hQ hGQ
  omega

omit [M.Loopless] in
open Classical in
private theorem gap_sum {P Q : Set α} (hP : M.IsFlat P) (hQ : M.IsFlat Q)
    (hPQ : P ⊂ Q) (hr : rank M Q = rank M P + 2) (f : Forms M) :
    let T := (Finset.univ : Finset (ProperFlat M)).filter fun F => P ⊂ F.1 ∧ F.1 ⊂ Q
    (∑ G ∈ T, f.1 G.1) + f.1 P = (T.card : ℝ) * f.1 P + f.1 Q := by
  intro T
  have incidence (i : α) :
      (∑ G ∈ T, indicator i G.1) + indicator i P =
        (T.card : ℝ) * indicator i P + indicator i Q := by
    by_cases hiP : i ∈ P
    · have h (G : ProperFlat M) (hG : G ∈ T) : indicator i G.1 = 1 := by
        have hiG := (Finset.mem_filter.mp hG).2.1.le hiP
        simp [indicator, hiG]
      rw [Finset.sum_congr rfl h]
      simp [indicator, hiP, hPQ.le hiP]
    by_cases hiQ : i ∈ Q
    · obtain ⟨F, hF, hiF, huniq⟩ := gap_partition M hP hQ hPQ hr ⟨hiQ, hiP⟩
      have hFT : F ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩
      rw [Finset.sum_eq_single_of_mem F hFT (fun G hG hne => by
        have hn : i ∉ G.1 := fun hiG => hne (huniq G (Finset.mem_filter.mp hG).2 hiG)
        simp [indicator, hn])]
      simp [indicator, hiP, hiQ, hiF]
    · have h (G : ProperFlat M) (hG : G ∈ T) : indicator i G.1 = 0 := by
        have hn : i ∉ G.1 := fun hiG => hiQ ((Finset.mem_filter.mp hG).2.2.le hiG)
        simp [indicator, hn]
      rw [Finset.sum_congr rfl h]
      simp [indicator, hiP, hiQ]
  obtain ⟨f, hf⟩ := f
  change (∑ G ∈ T, f G.1) + f P = (T.card : ℝ) * f P + f Q
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, _, j, _, rfl⟩ := hf
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    linear_combination incidence i - incidence j
  | zero => simp
  | add f g _ _ hf hg =>
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    linear_combination hf + hg
  | smul a f _ hf =>
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    linear_combination a * hf

private theorem top_balanced {r : ℕ} (hr : M.eRank = r + 1)
    (S : Finset (ProperFlat M)) (f : Forms M)
    (hf : ∀ G ∈ S, onFlats M f G = 0) :
    pair M (topFun M r) S (onFlats M f) = 0 := by
  classical
  by_cases hex : ∃ F : ProperFlat M, F ∉ S ∧ Chain M (insert F S) ∧
      (insert F S).card = r
  · obtain ⟨F, hF, hSF, hc⟩ := hex
    have hS := chain_mono M hSF (Finset.subset_insert _ _)
    obtain ⟨P, Q, hP, hQ, hPF, hFQ, hgap⟩ := exists_gap M hF hSF
    have hPflat : M.IsFlat P := by
      rcases hP with rfl | ⟨A, _, rfl⟩
      · exact empty_isFlat M
      · exact A.2.1
    have hQflat : M.IsFlat Q := by
      rcases hQ with rfl | ⟨A, _, rfl⟩
      · exact M.ground_isFlat
      · exact A.2.1
    have hPf : f.1 P = 0 := by
      rcases hP with rfl | ⟨A, hA, rfl⟩
      · exact (forms_endpoints M f).1
      · exact hf A hA
    have hQf : f.1 Q = 0 := by
      rcases hQ with rfl | ⟨A, hA, rfl⟩
      · exact (forms_endpoints M f).2
      · exact hf A hA
    have covered (n : ℕ) (hn₁ : 1 ≤ n) (hn₂ : n ≤ r) :
        ∃ G ∈ insert F S, rank M G.1 = n := by
      apply (Finset.mem_image (s := insert F S) (f := fun G => rank M G.1)).mp
      rw [rank_image_eq M hr hSF hc]
      exact Finset.mem_Icc.mpr ⟨hn₁, hn₂⟩
    have hFle := (Finset.mem_Icc.mp (rank_bounds M hr F)).2
    have hrPF := rank_lt M hPflat F.2.1 hPF
    have hrFQ := rank_lt M F.2.1 hQflat hFQ
    have hrQ : rank M Q ≤ r + 1 := by
      rw [← rank_ground M hr]
      exact rank_mono M hQflat.subset_ground
    have no_inside (n : ℕ) (hlo : rank M P < n) (hhi : n < rank M Q)
        (hn : n ≠ rank M F.1) : False := by
      obtain ⟨G, hG, hrG⟩ := covered n (by omega) (by omega)
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact hn hrG.symm
      · rcases hgap G hG with h | h
        · have := rank_mono M h
          omega
        · have := rank_mono M h
          omega
    have hrPQ : rank M Q = rank M P + 2 := by
      have h₁ : rank M F.1 = rank M P + 1 := by
        by_contra h
        exact no_inside (rank M P + 1) (by omega) (by omega) (by omega)
      have h₂ : rank M Q = rank M F.1 + 1 := by
        by_contra h
        exact no_inside (rank M F.1 + 1) (by omega) (by omega) (by omega)
      omega
    have qualifies (G : ProperFlat M) :
        (G ∉ S ∧ Chain M (insert G S) ∧ (insert G S).card = r) ↔
          P ⊂ G.1 ∧ G.1 ⊂ Q := by
      constructor
      · rintro ⟨hG, hSG, _⟩
        have hrG : rank M G.1 = rank M F.1 := by
          obtain ⟨A, hA, hrA⟩ := covered _ (Finset.mem_Icc.mp (rank_bounds M hr G)).1
            (Finset.mem_Icc.mp (rank_bounds M hr G)).2
          rcases Finset.mem_insert.mp hA with rfl | hA
          · exact hrA.symm
          · exact (hG ((rank_injOn M hSG (Finset.mem_insert_self _ _)
              (Finset.mem_insert_of_mem hA) hrA.symm).symm ▸ hA)).elim
        constructor
        · rcases hP with rfl | ⟨A, hA, rfl⟩
          · exact Set.empty_ssubset.mpr G.2.2.1
          · have hcmp := hSG A (Finset.mem_insert_of_mem hA) G (Finset.mem_insert_self _ _)
            exact (le_of_rank_le M hcmp (by omega)).ssubset_of_ne fun h =>
              hG (Subtype.ext h ▸ hA)
        · rcases hQ with rfl | ⟨A, hA, rfl⟩
          · exact G.2.1.subset_ground.ssubset_of_ne G.2.2.2
          · have hcmp := hSG G (Finset.mem_insert_self _ _) A (Finset.mem_insert_of_mem hA)
            exact (le_of_rank_le M hcmp (by omega)).ssubset_of_ne fun h =>
              hG (Subtype.ext h.symm ▸ hA)
      · rintro ⟨hPG, hGQ⟩
        have hG : G ∉ S := fun h =>
          (hgap G h).elim hPG.not_ge hGQ.not_ge
        exact ⟨hG, chain_insert M hS (fun A hA => (hgap A hA).elim
          (fun h => Or.inr (h.trans hPG.le)) (fun h => Or.inl (hGQ.le.trans h))),
          (Finset.card_insert_of_notMem hG).trans ((Finset.card_insert_of_notMem hF).symm.trans hc)⟩
    have he (G : ProperFlat M) : extend M (topFun M r) S G =
        if P ⊂ G.1 ∧ G.1 ⊂ Q then 1 else 0 := by
      by_cases hG : G ∈ S
      · have h : ¬ (P ⊂ G.1 ∧ G.1 ⊂ Q) := fun h => (qualifies G).mpr h |>.1 hG
        simp [extend, hG, h]
      · simp only [extend, topFun, ite_eq_right hG]
        by_cases h : Chain M (insert G S) ∧ (insert G S).card = r
        · simp only [ite_eq_left h, ite_eq_left ((qualifies G).mp ⟨hG, h⟩)]
        · simp only [ite_eq_right h, ite_eq_right (fun h' => h ((qualifies G).mpr h').2)]
    simpa [pair, he, ite_mul, ← Finset.sum_filter, hPf, hQf, onFlats] using
      gap_sum M hPflat hQflat (hPF.trans hFQ) hrPQ f
  · have hz (G : ProperFlat M) : extend M (topFun M r) S G = 0 := by
      by_cases hG : G ∈ S
      · simp [extend, hG]
      · have h : ¬ (Chain M (insert G S) ∧ (insert G S).card = r) :=
          fun h => hex ⟨G, hG, h⟩
        simp only [extend, topFun, ite_eq_right hG, ite_eq_right h]
    simp [pair, hz]

private def topWeight {r : ℕ} (hr : M.eRank = r + 1) : Weights M :=
  ⟨topFun M r, fun _ hS => ite_eq_right (fun h => hS h.1), top_balanced M hr⟩

end TopWeight

section ChowAction

variable [M.Finite]

private abbrev Operators :=
  Algebra.adjoin ℝ (Set.range fun F => cap M (delta M F))

private instance operators_commutative : IsMulCommutative (Operators M) :=
  Algebra.isMulCommutative_adjoin ℝ (by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
    exact cap_commute M (delta M F) (delta M G))

open scoped IsMulCommutative

private def polyAction : MvPolynomial (ProperFlat M) ℝ →ₐ[ℝ] Operators M :=
  aeval fun F => ⟨cap M (delta M F), Algebra.subset_adjoin ⟨F, rfl⟩⟩

private theorem polyAction_X (F : ProperFlat M) :
    (polyAction M (X F)).1 = cap M (delta M F) := by
  simp [polyAction]

private theorem flatFun_sum_delta (u : FlatFun M) :
    (∑ F, u F • delta M F) = u := by
  ext G
  simp [Finset.sum_apply, delta, mul_ite]

private theorem cap_onFlats (f : Forms M) : cap M (onFlats M f) = 0 := by
  ext w S
  exact congrFun (intersection_form M w f) S

private def alphaPolynomial (i : α) : MvPolynomial (ProperFlat M) ℝ :=
  ∑ᶠ (F : ProperFlat M) (_ : i ∈ F.1), X F

private theorem polyAction_alphaPolynomial (i : α) :
    (polyAction M (alphaPolynomial M i)).1 =
      cap M (fun F => indicator i F.1) := by
  classical
  let A := (Operators M).val.comp (polyAction M)
  have h (F : ProperFlat M) :
      A (if i ∈ F.1 then X F else 0) =
        capLinear M (indicator i F.1 • delta M F) := by
    by_cases hi : i ∈ F.1
    · simp only [hi, ite_true, indicator, one_smul]
      exact polyAction_X M F
    · simp [hi, indicator, A]
  change A (alphaPolynomial M i) = _
  simp only [alphaPolynomial, finsum_eq_if, finsum_eq_sum_of_fintype]
  rw [map_sum]
  simp only [h, ← map_sum, flatFun_sum_delta]
  rfl

private theorem polyAction_vanishes (p : MvPolynomial (ProperFlat M) ℝ)
    (hp : p ∈ chowIdeal M) : polyAction M p = 0 := by
  suffices h : chowIdeal M ≤ RingHom.ker (polyAction M).toRingHom from h hp
  unfold chowIdeal
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨F, G, hFG, hGF, rfl⟩
    apply Subtype.ext
    change ((polyAction M (X F * X G)).1 : Module.End ℝ (Weights M)) = 0
    rw [map_mul, Subalgebra.coe_mul, polyAction_X, polyAction_X, cap_delta_incomp M hFG hGF]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, j, hj, _, rfl⟩
    apply Subtype.ext
    let A := (Operators M).val.comp (polyAction M)
    change A (alphaPolynomial M i - alphaPolynomial M j) = 0
    rw [map_sub]
    change (polyAction M (alphaPolynomial M i)).1 -
      (polyAction M (alphaPolynomial M j)).1 = 0
    rw [polyAction_alphaPolynomial, polyAction_alphaPolynomial]
    let f : Forms M := ⟨_, diff_mem_forms M hi hj⟩
    have h := cap_onFlats M f
    change capLinear M ((fun F => indicator i F.1) - (fun F => indicator j F.1)) = 0 at h
    rwa [map_sub] at h

private def chowAction : ChowRing M →ₐ[ℝ] Module.End ℝ (Weights M) :=
  (Operators M).val.comp (Ideal.Quotient.liftₐ _ (polyAction M) (polyAction_vanishes M))

private theorem chowAction_mk (p : MvPolynomial (ProperFlat M) ℝ) :
    chowAction M (Ideal.Quotient.mkₐ ℝ (chowIdeal M) p) = (polyAction M p).1 := rfl

private theorem chowAction_x (F : ProperFlat M) :
    chowAction M (x M F) = cap M (delta M F) :=
  polyAction_X M F

private def squarefree (S : Finset (ProperFlat M)) : ChowRing M := ∏ F ∈ S, x M F

omit [M.Finite] in
private theorem squarefree_insert {S : Finset (ProperFlat M)} {F : ProperFlat M}
    (hF : F ∉ S) : squarefree M (insert F S) = x M F * squarefree M S :=
  Finset.prod_insert hF

private theorem action_squarefree (w : Weights M) {S T : Finset (ProperFlat M)}
    (h : Disjoint S T) :
    (chowAction M (squarefree M S) w).1 T = w.1 (S ∪ T) := by
  induction S using Finset.induction_on generalizing T w with
  | empty => simp [squarefree]
  | @insert F S hF ih =>
    have hFT := (Finset.disjoint_insert_left.mp h).1
    rw [squarefree_insert M hF, mul_comm, map_mul]
    change (chowAction M (squarefree M S) (chowAction M (x M F) w)).1 T = _
    rw [ih _ (Finset.disjoint_insert_left.mp h).2, chowAction_x, cap_delta_of_notMem]
    · rw [Finset.insert_union]
    · simp [hF, hFT]

private def Shifts (D : Module.End ℝ (Weights M)) (q : ℕ) : Prop :=
  ∀ (w : Weights M) (n : ℕ), (∀ S, S.card ≠ n → w.1 S = 0) →
    ∀ S, S.card + q ≠ n → (D w).1 S = 0

private theorem shifts_cap (u : FlatFun M) : Shifts M (cap M u) 1 := by
  intro w n hw S hS
  change intersection M u w S = 0
  have hz (G : ProperFlat M) : extend M w.1 S G = 0 := by
    by_cases hG : G ∈ S
    · simp [extend, hG]
    · rw [extend, ite_eq_right hG]
      exact hw _ (by rwa [Finset.card_insert_of_notMem hG])
  simp [intersection, pair, hz]

private theorem shifts_mul {D E : Module.End ℝ (Weights M)} {q k : ℕ}
    (hD : Shifts M D q) (hE : Shifts M E k) : Shifts M (D * E) (q + k) := by
  intro w n hw S hS
  by_cases hkn : k ≤ n
  · apply hD (E w) (n - k) (fun T hT => hE w n hw T (by omega)) S
    omega
  · have h : E w = 0 := by
      apply Subtype.ext
      funext T
      exact hE w n hw T (by omega)
    change (D (E w)).1 S = 0
    simp [h]

private theorem shifts_prod {ι : Type*} (s : Finset ι) (D : ι → Operators M) (q : ι → ℕ)
    (hD : ∀ i ∈ s, Shifts M (D i).1 (q i)) :
    Shifts M (∏ i ∈ s, D i).1 (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro w n hw S hS
    simp only [Finset.prod_empty, Subalgebra.coe_one, one_apply_eq_self]
    exact hw S (by simpa using hS)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Subalgebra.coe_mul, Finset.sum_insert hi]
    exact shifts_mul M (hD i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hD j (Finset.mem_insert_of_mem hj)))

private theorem shifts_pow {D : Module.End ℝ (Weights M)} (hD : Shifts M D 1) (n : ℕ) :
    Shifts M (D ^ n) n := by
  induction n with
  | zero =>
    intro w k hw S hS
    simpa using hw S (by simpa using hS)
  | succ n ih =>
    rw [pow_succ]
    exact shifts_mul M ih hD

private theorem shifts_C (a : ℝ) : Shifts M (polyAction M (C a)).1 0 := by
  intro w n hw S hS
  have h : (polyAction M (C a)).1 = algebraMap ℝ (Module.End ℝ (Weights M)) a :=
    (chowAction M).commutes a
  rw [h]
  change a * w.1 S = 0
  rw [hw S (by simpa using hS), mul_zero]

private theorem shifts_homogeneous {p : MvPolynomial (ProperFlat M) ℝ} {q : ℕ}
    (hp : p.IsHomogeneous q) : Shifts M (polyAction M p).1 q := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero =>
    intro w n hw S hS
    simp
  | add p p' _ _ h h' =>
    intro w n hw S hS
    rw [map_add, Subalgebra.coe_add]
    change ((polyAction M p).1 w).1 S + ((polyAction M p').1 w).1 S = 0
    rw [h w n hw S hS, h' w n hw S hS, add_zero]
  | monomial d a hd =>
    have he : (∑ F ∈ d.support, d F) = q := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hd
    rw [monomial_eq, Finsupp.prod, map_mul, Subalgebra.coe_mul, map_prod, ← he,
      ← zero_add (∑ F ∈ d.support, d F)]
    apply shifts_mul M (shifts_C M a)
    exact shifts_prod M d.support (fun F => polyAction M (X F ^ d F)) d (fun F _ => by
      rw [map_pow, Subalgebra.coe_pow, polyAction_X]
      exact shifts_pow M (shifts_cap M _) _)

end ChowAction

section Uniqueness

variable [M.Finite]

private def weightedVars : FlatFun M →ₗ[ℝ] ChowRing M where
  toFun u := ∑ F, u F • x M F
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a u := by simp [Finset.smul_sum, mul_smul]

private theorem weightedVars_delta (F : ProperFlat M) :
    weightedVars M (delta M F) = x M F := by
  simp [weightedVars, delta, ite_smul]

private theorem weightedVars_onFlats (f : Forms M) : weightedVars M (onFlats M f) = 0 := by
  classical
  have alpha (i : α) : weightedVars M (fun F => indicator i F.1) = alphaClass M i := by
    simp [weightedVars, indicator, alphaClass, x, finsum_eq_if, finsum_eq_sum_of_fintype,
      apply_ite, ite_smul]
  obtain ⟨f, hf⟩ := f
  change weightedVars M (fun F => f F.1) = 0
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, j, hj, rfl⟩ := hf
    change weightedVars M ((fun F => indicator i F.1) - (fun F => indicator j F.1)) = 0
    rw [map_sub, alpha, alpha, alphaClass_eq M hi hj, sub_self]
  | zero => exact map_zero _
  | add f g _ _ hf hg =>
    change weightedVars M ((fun F => f F.1) + (fun F => g F.1)) = 0
    rw [map_add, hf, hg, add_zero]
  | smul a f _ hf =>
    change weightedVars M (a • fun F => f F.1) = 0
    rw [map_smul, hf, smul_zero]

omit [M.Finite] in
private theorem squarefree_eq_zero {S : Finset (ProperFlat M)} (hS : ¬ Chain M S) :
    squarefree M S = 0 := by
  change ¬ (∀ F ∈ S, ∀ G ∈ S, F.1 ⊆ G.1 ∨ G.1 ⊆ F.1) at hS
  push Not at hS
  obtain ⟨F, hF, G, hG, hFG, hGF⟩ := hS
  have hne : G ≠ F := by
    intro h
    subst G
    exact hFG (fun _ h => h)
  rw [squarefree, ← Finset.prod_erase_mul S (x M) hF,
    ← Finset.prod_erase_mul (S.erase F) (x M) (Finset.mem_erase.mpr ⟨hne, hG⟩),
    mul_assoc, x_mul_x_eq_zero_of_incomparable M hGF hFG, mul_zero]

omit [M.Finite] in
private theorem squarefree_mem (S : Finset (ProperFlat M)) :
    squarefree M S ∈ gradedPiece M S.card := by
  refine ⟨∏ F ∈ S, X F, ?_, ?_⟩
  · simpa using IsHomogeneous.prod S (fun F => (X F : MvPolynomial (ProperFlat M) ℝ))
      (fun _ => 1) (fun F _ => isHomogeneous_X ℝ F)
  · simp [squarefree, x]

private def probe (d : ChowRing M →ₗ[ℝ] ℝ) (p : ChowRing M) : WeightFun M :=
  fun S => d (p * squarefree M S)

private theorem pair_probe (d : ChowRing M →ₗ[ℝ] ℝ) (p : ChowRing M)
    (S : Finset (ProperFlat M)) (u : FlatFun M) (hu : ∀ F ∈ S, u F = 0) :
    pair M (probe M d p) S u = d (p * squarefree M S * weightedVars M u) := by
  simp only [pair, weightedVars, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : F ∈ S
  · simp [extend, hF, hu F hF]
  · rw [extend, ite_eq_right hF, probe, squarefree_insert M hF, mul_smul_comm,
      map_smul, smul_eq_mul, mul_comm (u F)]
    congr 2
    ac_rfl

private def probeWeight (d : ChowRing M →ₗ[ℝ] ℝ) (p : ChowRing M) : Weights M :=
  ⟨probe M d p, fun S hS => by simp [probe, squarefree_eq_zero M hS],
    fun S f hf => by rw [pair_probe M d p S _ hf, weightedVars_onFlats, mul_zero, map_zero]⟩

private theorem probe_mul_x (d : ChowRing M →ₗ[ℝ] ℝ) (p : ChowRing M) (F : ProperFlat M) :
    probeWeight M d (p * x M F) = cap M (delta M F) (probeWeight M d p) := by
  ext S
  by_cases hS : Chain M S
  · let f := interpolant M S (delta M F)
    have hf : ∀ G ∈ S, (delta M F - onFlats M f) G = 0 := fun G hG => by
      simp [f, interpolant_eq M hS _ hG]
    change d ((p * x M F) * squarefree M S) =
      pair M (probe M d p) S (delta M F - onFlats M f)
    rw [pair_probe M d p S _ hf, map_sub, weightedVars_onFlats, sub_zero, weightedVars_delta]
    ac_rfl
  · exact ((probeWeight M d (p * x M F)).2.1 _ hS).trans
      ((cap M (delta M F) (probeWeight M d p)).2.1 _ hS).symm

private theorem probe_weight_polynomial (d : ChowRing M →ₗ[ℝ] ℝ)
    (p : MvPolynomial (ProperFlat M) ℝ) :
    probeWeight M d (Ideal.Quotient.mkₐ ℝ (chowIdeal M) p) =
      (polyAction M p).1 (probeWeight M d 1) := by
  let Q := Ideal.Quotient.mkₐ ℝ (chowIdeal M)
  let A := (Operators M).val.comp (polyAction M)
  change probeWeight M d (Q p) = A p (probeWeight M d 1)
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show C a = algebraMap ℝ (MvPolynomial (ProperFlat M) ℝ) a from rfl,
      Q.commutes, A.commutes]
    ext S
    change d (algebraMap ℝ (ChowRing M) a * squarefree M S) =
      a * d (1 * squarefree M S)
    simp [← Algebra.smul_def]
  | add p q hp hq =>
    rw [map_add, map_add]
    have h : probeWeight M d (Q p + Q q) = probeWeight M d (Q p) + probeWeight M d (Q q) := by
      ext S
      change d ((Q p + Q q) * squarefree M S) =
        d (Q p * squarefree M S) + d (Q q * squarefree M S)
      rw [add_mul, map_add]
    rw [h, hp, hq]
    rfl
  | mul_X p F hp =>
    rw [map_mul, map_mul]
    have hX : A (X F) = cap M (delta M F) := polyAction_X M F
    rw [hX]
    change probeWeight M d (Q p * x M F) = (A p * cap M (delta M F)) (probeWeight M d 1)
    have commute : Commute (A p) (cap M (delta M F)) := by
      have h : Commute (polyAction M p) (polyAction M (X F)) :=
        mul_comm' _ _
      have h' : Commute (A p) (A (X F)) := h.map (Operators M).val
      rwa [hX] at h'
    rw [probe_mul_x, hp, commute.eq]
    rfl

private theorem squarefree_eq_flag {S : Finset (ProperFlat M)} (hS : Chain M S) {r : ℕ}
    (hc : S.card = r) :
    ∃ F : Fin r → ProperFlat M, StrictMono (fun i => (F i).1) ∧
      squarefree M S = ∏ i, x M (F i) := by
  let order : LinearOrder S := LinearOrder.lift' (fun F : S => rank M F.1.1)
    (fun F G h => Subtype.ext (rank_injOn M hS F.2 G.2 h))
  let e := @Fintype.orderIsoFinOfCardEq S order _ r (by simpa using hc)
  refine ⟨fun i => (e i).1, fun i j hij => ?_, ?_⟩
  · have he := @OrderIso.strictMono (Fin r) S _ order.toPreorder e i j hij
    change rank M (e i).1.1 < rank M (e j).1.1 at he
    have hle := le_of_rank_le M (hS _ (e i).2 _ (e j).2) he.le
    exact hle.ssubset_of_ne (fun h => he.ne (congrArg (rank M) h))
  · rw [squarefree, ← Finset.prod_coe_sort S (x M)]
    exact (Fintype.prod_equiv e.toEquiv _ _ (fun _ => rfl)).symm

variable [M.Loopless]

private theorem probe_one {r : ℕ} (hr : M.eRank = r + 1)
    (d : ChowRing M →ₗ[ℝ] ℝ) (hd : IsDegreeMap M r d) :
    probeWeight M d 1 = topWeight M hr := by
  ext S
  change d (1 * squarefree M S) = topFun M r S
  rw [one_mul]
  by_cases hS : Chain M S
  · by_cases hc : S.card = r
    · obtain ⟨F, hF, he⟩ := squarefree_eq_flag M hS hc
      rw [he, hd.2 F hF]
      exact (ite_eq_left ⟨hS, hc⟩).symm
    · rw [hd.1 _ hc _ (squarefree_mem M S)]
      exact (ite_eq_right (fun h => hc h.2)).symm
  · rw [squarefree_eq_zero M hS, map_zero]
    exact (ite_eq_right (fun h => hS h.1)).symm

end Uniqueness

section DegreeMap

variable [M.Finite] [M.Loopless]

private def degree {r : ℕ} (hr : M.eRank = r + 1) : ChowRing M →ₗ[ℝ] ℝ where
  toFun p := (chowAction M p (topWeight M hr)).1 ∅
  map_add' p q := by rw [map_add]; rfl
  map_smul' a p := by rw [map_smul]; rfl

omit [M.Finite] [M.Loopless] in
private theorem flag_image {r : ℕ} (F : Fin r → ProperFlat M)
    (hF : StrictMono (fun i => (F i).1)) :
    let S := Finset.univ.image F
    Chain M S ∧ S.card = r ∧ squarefree M S = ∏ i, x M (F i) := by
  intro S
  have hinj : Function.Injective F := fun i j h => hF.injective (congrArg Subtype.val h)
  refine ⟨?_, by simp [S, Finset.card_image_of_injective _ hinj], Finset.prod_image hinj.injOn⟩
  intro G hG H hH
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hG
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hH
  exact (le_total i j).imp (fun h => hF.monotone h) (fun h => hF.monotone h)

private theorem degree_isDegreeMap {r : ℕ} (hr : M.eRank = r + 1) :
    IsDegreeMap M r (degree M hr) := by
  constructor
  · rintro q hq _ ⟨p, hp, rfl⟩
    change (chowAction M (Ideal.Quotient.mkₐ ℝ (chowIdeal M) p) (topWeight M hr)).1 ∅ = 0
    rw [chowAction_mk]
    apply shifts_homogeneous M (mem_homogeneousSubmodule _ _ |>.mp hp) _ r
    · exact fun S hS => ite_eq_right (fun h => hS h.2)
    · simpa using hq
  · intro F hF
    obtain ⟨hS, hc, he⟩ := flag_image M F hF
    rw [← he]
    change (chowAction M (squarefree M (Finset.univ.image F)) (topWeight M hr)).1 ∅ = 1
    rw [action_squarefree M _ (Finset.disjoint_empty_right _), Finset.union_empty]
    exact ite_eq_left ⟨hS, hc⟩

private theorem degree_unique {r : ℕ} (hr : M.eRank = r + 1)
    (d : ChowRing M →ₗ[ℝ] ℝ) (hd : IsDegreeMap M r d) : d = degree M hr := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℝ (chowIdeal M) a
  let q := Ideal.Quotient.mkₐ ℝ (chowIdeal M) p
  have h : probeWeight M d q = chowAction M q (topWeight M hr) := by
    unfold q
    rw [chowAction_mk, ← probe_one M hr d hd]
    exact probe_weight_polynomial M d p
  have he : d (q * 1) = degree M hr q := congrArg (fun w : Weights M => w.1 ∅) h
  simpa only [mul_one] using he

end DegreeMap

end

/-- **The degree map of a matroid** (Adiprasito, Huh and Katz, *Hodge theory for combinatorial
geometries*, Ann. of Math. 188 (2018), Definition 5.9 and Proposition 5.10). For a finite
loopless matroid `M` of rank `r + 1` there is exactly one linear map `deg : A*(M)_ℝ → ℝ` that
vanishes on the graded pieces `A^q(M)_ℝ` with `q ≠ r` and takes the value `1` on
`x_{F₁} ⋯ x_{F_r}` for every flag `F₁ ⊊ ⋯ ⊊ F_r` of nonempty proper flats.

Adiprasito, Huh and Katz also prove that their degree map `A^r(Σ_M) → ℤ`, on the integral Chow
ring of the Bergman fan `Σ_M`, is an isomorphism (Proposition 5.10); that assertion is not part of
this statement. -/
public theorem existsUnique_isDegreeMap {α : Type*} (M : _root_.Matroid α) [M.Finite]
    [M.Loopless] (r : ℕ) (hr : M.eRank = r + 1) :
    ∃! deg : ChowRing M →ₗ[ℝ] ℝ, IsDegreeMap M r deg := by
  exact ⟨degree M hr, degree_isDegreeMap M hr, degree_unique M hr⟩

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted
