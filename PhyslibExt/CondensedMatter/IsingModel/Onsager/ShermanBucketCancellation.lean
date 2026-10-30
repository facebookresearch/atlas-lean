/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanGenericCancellation
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFirstReturnFactor
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanReroot

/-!

# The first-return bucket series

The series of closed walks through a dart, avoiding its reverse, equals `-log (1 - z)` for the total
first-return weight `z`.

## i. Overview

Rooted lists `[v₀, …, vₙ, e]` with `v₀ = e` that avoid `r` correspond to rooted closed walks of
length `n + 1`, and the rooted list series reorganizes by length into
`∑ₙ ∑_{v₀ = e, v avoids r} weight(v) / visits(v)`. By rerooting, this is the series of all closed
walks through `e` avoiding `r` divided by their length. With `ons_rootedListSeries_eq_geometric` the
bucket series becomes `∑ₖ z ^ (k + 1) / (k + 1)`, where `z` is the total weight of first-return
loops at `e`. Specialized to the Kac-Ward matrix with `r` the reverse dart, this gives the factor
`1 - λ` of Sherman's product formula with `λ` the first-return weight.

## ii. Key results

- `ons_rootedListSeries_eq_lengthSum` : the rooted list series as a sum by length
- `ons_loopBucketSeries_eq_geometric` : the bucket series is the logarithmic series in the
  first-return weight
- `ons_bucketESeries_eq_geometric` : the same for the Kac-Ward bucket `ons_bucketE`
- `ons_hlam_firstReturn` : the bucket exponential is `1 - λ` with `λ` the first-return weight

## iii. Table of contents

- A. Rooted lists as closed walks
- B. Bucket series
- C. The Kac-Ward bucket

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Rooted lists as closed walks -/

omit [Fintype E] [DecidableEq E] in
private lemma validRootedList_ofFn_append (e r : E) (her : e ≠ r)
    {n : ℕ} (v : Fin (n + 1) → E) :
    ons_validRootedList e r (List.ofFn v ++ [e]) ↔
      v 0 = e ∧ ∀ j, v j ≠ r := by
  unfold ons_validRootedList
  constructor
  · rintro ⟨hhead, _, havoid⟩
    have hroot : v 0 = e := by simpa [List.ofFn_succ] using hhead
    refine ⟨hroot, fun j => havoid (v j) ?_⟩
    rw [List.mem_append, List.mem_ofFn]
    exact Or.inl ⟨j, rfl⟩
  · rintro ⟨hroot, havoid⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [List.ofFn_succ] using hroot
    · rw [List.getLast?_append_of_ne_nil _ (by simp : [e] ≠ [])]
      simp
    · intro x hx
      rw [List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
      rcases hx with ⟨j, rfl⟩ | rfl
      · exact havoid j
      · exact her

private lemma rootedListTerm_ofFn_append (Lambda : Matrix E E ℂ) (e : E)
    {n : ℕ} (v : Fin (n + 1) → E) (hroot : v 0 = e) :
    ons_rootedListTerm Lambda e (List.ofFn v ++ [e]) =
      ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  unfold ons_rootedListTerm
  rw [ons_firstReturnFactors_length e v hroot]
  rw [ons_loopWeight_eq_edgeWeight, hroot]

omit [Fintype E] [DecidableEq E] in
private lemma ofFn_snoc (a : E) {n : ℕ} (v : Fin (n + 1) → E) :
    List.ofFn (Fin.snoc v a : Fin (n + 2) → E) = List.ofFn v ++ [a] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact List.concat_eq_append

/-- The rooted list term restricted to rooted closed walks at `e` avoiding `r`, and `0` elsewhere.
-/
private noncomputable def rootedIndicator (Lambda : Matrix E E ℂ) (e r : E)
    (w : List E) : ℂ :=
  Set.indicator {w | ons_validRootedList e r w}
    (ons_rootedListTerm Lambda e) w

omit [Fintype E] in
private lemma rootedIndicator_nil (Lambda : Matrix E E ℂ) (e r : E) :
    rootedIndicator Lambda e r [] = 0 := by
  classical
  simp [rootedIndicator, Set.indicator, ons_validRootedList]

omit [Fintype E] in
private lemma rootedIndicator_singleton (Lambda : Matrix E E ℂ)
    (e r a : E) : rootedIndicator Lambda e r [a] = 0 := by
  classical
  unfold rootedIndicator Set.indicator
  split_ifs
  · simp [ons_rootedListTerm, ons_firstReturnFactors, ons_firstReturnSplit]
  · rfl

private lemma rootedIndicator_ofFn_snoc (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r) {n : ℕ} (v : Fin (n + 1) → E) :
    rootedIndicator Lambda e r
        (List.ofFn (Fin.snoc v e : Fin (n + 2) → E)) =
      if v 0 = e ∧ ∀ j, v j ≠ r then
        ons_loopWeight Lambda v / (ons_visitCount e v : ℂ)
      else 0 := by
  classical
  rw [ofFn_snoc]
  unfold rootedIndicator Set.indicator
  change (if ons_validRootedList e r (List.ofFn v ++ [e]) then
      ons_rootedListTerm Lambda e (List.ofFn v ++ [e]) else 0) = _
  rw [validRootedList_ofFn_append e r her v]
  split_ifs with h
  · exact rootedListTerm_ofFn_append Lambda e v h.1
  · rfl

omit [Fintype E] in
private lemma rootedIndicator_ofFn_snoc_ne (Lambda : Matrix E E ℂ)
    (e r a : E) (ha : a ≠ e) {n : ℕ} (v : Fin (n + 1) → E) :
    rootedIndicator Lambda e r
        (List.ofFn (Fin.snoc v a : Fin (n + 2) → E)) = 0 := by
  classical
  unfold rootedIndicator Set.indicator
  rw [ite_eq_right]
  intro hvalid
  have hlast := hvalid.2.1
  rw [ofFn_snoc,
    List.getLast?_append_of_ne_nil _ (by simp : [a] ≠ [])] at hlast
  simp only [List.getLast?_singleton, Option.some.injEq] at hlast
  exact ha hlast

private lemma sum_rootedIndicator_length (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r) (n : ℕ) :
    (∑ f : Fin (n + 2) → E,
        rootedIndicator Lambda e r (List.ofFn f)) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E =>
          v 0 = e ∧ ∀ j, v j ≠ r),
        ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  classical
  let snocEquiv : E × (Fin (n + 1) → E) ≃ (Fin (n + 2) → E) :=
    Fin.snocEquiv (fun _ : Fin (n + 2) => E)
  calc
    (∑ f : Fin (n + 2) → E,
        rootedIndicator Lambda e r (List.ofFn f)) =
        ∑ p : E × (Fin (n + 1) → E),
          rootedIndicator Lambda e r (List.ofFn (snocEquiv p)) := by
            exact (Equiv.sum_comp snocEquiv
              (fun f => rootedIndicator Lambda e r (List.ofFn f))).symm
    _ = ∑ v : Fin (n + 1) → E,
          rootedIndicator Lambda e r
            (List.ofFn (Fin.snoc v e : Fin (n + 2) → E)) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_eq_single e
          · intro a _ ha
            apply Finset.sum_eq_zero
            intro v _
            exact rootedIndicator_ofFn_snoc_ne Lambda e r a ha v
          · simp
    _ = _ := by
      simp_rw [rootedIndicator_ofFn_snoc Lambda e r her]
      rw [Finset.sum_filter]

/-! ## B. Bucket series -/

lemma ons_rootedListSeries_eq_lengthSum (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    (∑' w : {w : List E // ons_validRootedList e r w},
        ons_rootedListTerm Lambda e w.1) =
      ∑' n : ℕ, ∑ v ∈ Finset.univ.filter
          (fun v : Fin (n + 1) → E => v 0 = e ∧ ∀ j, v j ≠ r),
        ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  classical
  let F : List E → ℂ := rootedIndicator Lambda e r
  let equiv : (Sigma fun m : ℕ => Fin m → E) ≃ List E :=
    (List.equivSigmaTuple : List E ≃ Sigma fun m : ℕ => Fin m → E).symm
  have hroot := ons_summable_rootedListTerm Lambda e r her hsum hsmall
  have hF : Summable F := by
    have hind : Summable (Set.indicator
        {w : List E | ons_validRootedList e r w}
        (ons_rootedListTerm Lambda e)) :=
      summable_subtype_iff_indicator.mp hroot
    exact hind
  have hsigma : Summable (F ∘ equiv) := equiv.summable_iff.mpr hF
  let G : ℕ → ℂ := fun m => ∑' f : Fin m → E, F (List.ofFn f)
  have houter : Summable G := by
    have hs := hsigma.sigma
    simpa only [G, equiv, List.equivSigmaTuple_symm_apply,
      Function.comp_apply] using hs
  have hG0 : G 0 = 0 := by
    change (∑' f : Fin 0 → E, F (List.ofFn f)) = 0
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro f _
    have hf : f = Fin.elim0 := Subsingleton.elim _ _
    subst f
    simpa using rootedIndicator_nil Lambda e r
  have hG1 : G 1 = 0 := by
    change (∑' f : Fin 1 → E, F (List.ofFn f)) = 0
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro f _
    rw [show List.ofFn f = [f 0] by simp [List.ofFn_succ]]
    exact rootedIndicator_singleton Lambda e r (f 0)
  calc
    (∑' w : {w : List E // ons_validRootedList e r w},
        ons_rootedListTerm Lambda e w.1) = ∑' w : List E, F w := by
          exact
            tsum_subtype {w : List E | ons_validRootedList e r w}
              (ons_rootedListTerm Lambda e)
    _ = ∑' p : Sigma fun m : ℕ => Fin m → E, F (equiv p) := by
          exact (equiv.tsum_eq F).symm
    _ = ∑' m : ℕ, G m := by
          simpa only [Function.comp_apply, G, equiv,
            List.equivSigmaTuple_symm_apply] using hsigma.tsum_sigma
    _ = ∑' n : ℕ, G (n + 1 + 1) := by
          have hprefix : ∑ i ∈ Finset.range 2, G i = 0 := by
            norm_num [Finset.sum_range_succ, hG0, hG1]
          have htail := houter.sum_add_tsum_nat_add 2
          rw [hprefix, zero_add] at htail
          simpa [Nat.add_assoc] using htail.symm
    _ = _ := by
      apply tsum_congr
      intro n
      change (∑' f : Fin (n + 2) → E,
        F (List.ofFn f)) = _
      rw [tsum_fintype]
      exact sum_rootedIndicator_length Lambda e r her n

lemma ons_summable_rootedLengthSum (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    Summable fun n : ℕ =>
      ∑ v ∈ Finset.univ.filter
          (fun v : Fin (n + 1) → E => v 0 = e ∧ ∀ j, v j ≠ r),
        ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  classical
  let F : List E → ℂ := rootedIndicator Lambda e r
  let equiv : (Sigma fun m : ℕ => Fin m → E) ≃ List E :=
    (List.equivSigmaTuple : List E ≃ Sigma fun m : ℕ => Fin m → E).symm
  have hroot := ons_summable_rootedListTerm Lambda e r her hsum hsmall
  have hF : Summable F := by
    have hind : Summable (Set.indicator
        {w : List E | ons_validRootedList e r w}
        (ons_rootedListTerm Lambda e)) :=
      summable_subtype_iff_indicator.mp hroot
    exact hind
  have hsigma : Summable (F ∘ equiv) := equiv.summable_iff.mpr hF
  let G : ℕ → ℂ := fun m => ∑' f : Fin m → E, F (List.ofFn f)
  have houter : Summable G := by
    have hs := hsigma.sigma
    simpa only [G, equiv, List.equivSigmaTuple_symm_apply,
      Function.comp_apply] using hs
  have htail : Summable fun n => G (n + 2) :=
    (summable_nat_add_iff 2).2 houter
  apply htail.congr
  intro n
  change (∑' f : Fin (n + 2) → E, F (List.ofFn f)) = _
  rw [tsum_fintype]
  exact sum_rootedIndicator_length Lambda e r her n

lemma ons_loopBucketSeries_eq_geometric (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    (∑' n : ℕ,
        (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E =>
            (∃ k, v k = e) ∧ ∀ j, v j ≠ r),
          ons_loopWeight Lambda v) / ((n : ℂ) + 1)) =
      ∑' k : ℕ,
        (∑' s, ons_firstReturnWeight Lambda e r s) ^ (k + 1) / (k + 1) := by
  calc
    (∑' n : ℕ,
        (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E =>
            (∃ k, v k = e) ∧ ∀ j, v j ≠ r),
          ons_loopWeight Lambda v) / ((n : ℂ) + 1)) =
        ∑' n : ℕ, ∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → E => v 0 = e ∧ ∀ j, v j ≠ r),
          ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
            apply tsum_congr
            intro n
            simpa [Nat.cast_add, Nat.cast_one] using
              (ons_loopSum_div_length_eq_rerooted
                (n := n + 1) Lambda e r)
    _ = (∑' w : {w : List E // ons_validRootedList e r w},
          ons_rootedListTerm Lambda e w.1) :=
      (ons_rootedListSeries_eq_lengthSum Lambda e r her hsum hsmall).symm
    _ = _ := ons_rootedListSeries_eq_geometric Lambda e r her hsum hsmall

lemma ons_summable_loopBucketSeries (Lambda : Matrix E E ℂ)
    (e r : E) (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    Summable fun n : ℕ =>
      (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E =>
          (∃ k, v k = e) ∧ ∀ j, v j ≠ r),
        ons_loopWeight Lambda v) / ((n : ℂ) + 1) := by
  have hrooted :=
    ons_summable_rootedLengthSum Lambda e r her hsum hsmall
  apply hrooted.congr
  intro n
  symm
  simpa [Nat.cast_add, Nat.cast_one] using
    (ons_loopSum_div_length_eq_rerooted (n := n + 1) Lambda e r)

/-! ## C. The Kac-Ward bucket -/

lemma ons_bucketESeries_eq_geometric {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
    (∑' n : ℕ, ons_bucketE L x omega e n / ((n : ℂ) + 1)) =
      ∑' k : ℕ,
        (∑' s, ons_firstReturnWeight
          (ons_KWmat L x omega) e (ons_dartRev L e) s) ^ (k + 1) / (k + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_bucketE, not_exists] using
    ons_loopBucketSeries_eq_geometric
      (ons_KWmat L x omega) e (ons_dartRev L e) her hsum hsmall

lemma ons_summable_bucketE_firstReturn {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
    Summable fun n : ℕ =>
      ons_bucketE L x omega e n / ((n : ℂ) + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_bucketE, not_exists] using
    ons_summable_loopBucketSeries
      (ons_KWmat L x omega) e (ons_dartRev L e) her hsum hsmall

lemma ons_hlam_firstReturn {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
    Complex.exp (- ∑' n : ℕ,
        ons_bucketE L x omega e n / ((n : ℂ) + 1)) =
      1 - ∑' s,
        ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s := by
  let z := ∑' s,
    ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s
  have hz : ‖z‖ < 1 :=
    lt_of_le_of_lt (norm_tsum_le_tsum_norm hsum) hsmall
  rw [ons_bucketESeries_eq_geometric x omega e hsum hsmall]
  exact ons_lemma4_exp hz

end StatMech.Onsager
