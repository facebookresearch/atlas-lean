---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.closestPair_isAnswer
---

# Closest Pair is Answer

On a strip sorted by `y`, every pair whose squared `y` gap is below `δ` is compared. -/
theorem stripScan_lower (δ : 𝕜) (ys : List (𝕜 × 𝕜)) (hs : ys.Pairwise fun a b => a.2 ≤ b.2)
    (a b : 𝕜 × 𝕜) (hab : [a, b] <+ ys) (hgap : (b.2 - a.2) ^ 2 < δ) :
    ∃ d, (stripScan δ ys).ret = some d ∧ d ≤ dist2 a b := by
  induction ys with
  | nil => simp at hab
  | cons p ps ih =>
      simp only [stripScan, ret_bind, ret_pure]
      rcases pair_sublist_cons hab with h | ⟨rfl, hb⟩
      · exact optMin_le_right _ (ih hs.of_cons h)
      · exact optMin_le_left _ (scanFrom_lower δ a ps hs.of_cons
          (fun q hq => List.rel_of_pairwise_cons hs hq) b hb hgap)

/-! ## Divide and conquer -/

theorem closestRec_isAnswer (xs : List (𝕜 × 𝕜)) (hs : xs.Pairwise fun a b => a.1 ≤ b.1) :
    IsAnswer xs (closestRec xs).ret := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    rw [closestRec]
    split_ifs with hle
    · exact bruteMin_isAnswer xs
    · simp only [ret_bind]
      have hLR : xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) = xs :=
        List.take_append_drop _ _
      have hLlen : (xs.take (xs.length / 2)).length = xs.length / 2 := by
        simp only [List.length_take]; omega
      have hRlen : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 :=
        List.length_drop
      generalize xs.take (xs.length / 2) = L at hLR hLlen ⊢
      generalize xs.drop (xs.length / 2) = R at hLR hRlen ⊢
      have hsLR : (L ++ R).Pairwise fun a b => a.1 ≤ b.1 := by rw [hLR]; exact hs
      have hLsub : L <+ xs := hLR ▸ List.sublist_append_left L R
      have hRsub : R <+ xs := hLR ▸ List.sublist_append_right L R
      have ihL := ih L.length (by omega) L (hs.sublist hLsub) rfl
      have ihR := ih R.length (by omega) R (hs.sublist hRsub) rfl
      -- the right half has a pair, so both halves give a value
      obtain ⟨δ, hδ⟩ : ∃ δ, omin (closestRec L).ret (closestRec R).ret = some δ := by
        match R, hRlen, ihR with
        | a :: b :: rest, _, ihR =>
            obtain ⟨d, hd, -⟩ := ihR.lower a b (by simp)
            obtain ⟨δ, hδ, -⟩ := optMin_le_right (closestRec L).ret ⟨d, hd, le_refl d⟩
            exact ⟨δ, hδ⟩
        | [], h, _ => simp at h; omega
        | [_], h, _ => simp at h; omega
      rw [hδ]
      simp only [ret_bind, ret_pure]
      -- the halves bound every pair inside them by `δ`
      have hδL : ∀ p q, [p, q] <+ L → δ ≤ dist2 p q := fun p q hpq => by
        obtain ⟨δ', h1, h2⟩ := optMin_le_left (closestRec R).ret (ihL.lower p q hpq)
        rw [hδ, Option.some.injEq] at h1
        exact h1 ▸ h2
      have hδR : ∀ p q, [p, q] <+ R → δ ≤ dist2 p q := fun p q hpq => by
        obtain ⟨δ', h1, h2⟩ := optMin_le_right (closestRec L).ret (ihR.lower p q hpq)
        rw [hδ, Option.some.injEq] at h1
        exact h1 ▸ h2
      set xmid := (Option.map Prod.fst L.getLast?).getD 0 with hxmid
      set strip := xs.filter fun p => decide ((p.1 - xmid) ^ 2 < δ) with hstrip
      set ys := strip.mergeSort fun a b => decide (a.2 ≤ b.2) with hys
      have hperm : ys ~ strip := List.mergeSort_perm _ _
      have hsorted : ys.Pairwise fun a b => a.2 ≤ b.2 :=
        (List.pairwise_mergeSort (le := fun a b => decide (a.2 ≤ b.2))
          (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
          (fun a b => by simpa using le_total a.2 b.2) strip).imp (fun h => by simpa using h)
      constructor
      · intro d hd
        rcases optMin_eq_some hd with h1 | h1
        · rw [Option.some.injEq] at h1
          subst h1
          rcases optMin_eq_some hδ with h2 | h2
          · obtain ⟨p, q, hpq, hd⟩ := ihL.attained _ h2
            exact ⟨p, q, hpq.trans hLsub, hd⟩
          · obtain ⟨p, q, hpq, hd⟩ := ihR.attained _ h2
            exact ⟨p, q, hpq.trans hRsub, hd⟩
        · obtain ⟨a, b, hab, hd⟩ := stripScan_attained δ ys d h1
          rcases pair_sublist_of_perm hperm hab with h | h
          · exact ⟨a, b, h.trans List.filter_sublist, hd⟩
          · exact ⟨b, a, h.trans List.filter_sublist, by rw [dist2_comm]; exact hd⟩
      · intro p q hpq
        by_cases hle : δ ≤ dist2 p q
        · exact optMin_le_left _ ⟨δ, rfl, hle⟩
        refine optMin_le_right _ ?_
        rw [not_le] at hle
        obtain ⟨r₁, r₂, hr, h₁, h₂⟩ := List.sublist_append_iff.1 (hLR ▸ hpq)
        match r₁, hr with
        | [], hr =>
            simp only [List.nil_append] at hr
            exact absurd (hδR p q (hr ▸ h₂)) (not_le.2 hle)
        | [x, y], hr =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at hr
            obtain ⟨rfl, rfl, hr⟩ := hr
            exact absurd (hδL _ _ h₁) (not_le.2 hle)
        | _ :: _ :: _ :: _, hr => simp at hr
        | [x], hr =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            have hpL : p ∈ L := List.singleton_sublist.1 h₁
            have hqR : q ∈ R := List.singleton_sublist.1 h₂
            -- the dividing line separates `p` and `q`
            obtain ⟨L', l, hLl⟩ : ∃ L' l, L = L' ++ [l] := by
              rcases List.eq_nil_or_concat L with hL0 | ⟨L', l, hL'⟩
              · simp [hL0] at hpL
              · exact ⟨L', l, by rw [hL', List.concat_eq_append]⟩
            have hx : xmid = l.1 := by simp [hxmid, hLl]
            have hpl : p.1 ≤ l.1 := by
              rw [hLl] at hpL hsLR
              rcases List.mem_append.1 hpL with h | h
              · exact (List.pairwise_append.1 (List.pairwise_append.1 hsLR).1).2.2 p h l
                  List.mem_cons_self
              · rw [List.mem_singleton.1 h]
            have hlq : l.1 ≤ q.1 := (List.pairwise_append.1 hsLR).2.2 l
              (by rw [hLl]; simp) q hqR
            have hdx := sq_sub_fst_le_dist2 p q
            have hpstrip : (p.1 - xmid) ^ 2 < δ := by
              have : (p.1 - xmid) ^ 2 ≤ (p.1 - q.1) ^ 2 := by
                rw [hx, show (p.1 - l.1) ^ 2 = (l.1 - p.1) ^ 2 by ring,
                  show (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 by ring]
                exact pow_le_pow_left₀ (by linarith) (by linarith) 2
              linarith
            have hqstrip : (q.1 - xmid) ^ 2 < δ := by
              have : (q.1 - xmid) ^ 2 ≤ (p.1 - q.1) ^ 2 := by
                rw [hx, show (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 by ring]
                exact pow_le_pow_left₀ (by linarith) (by linarith) 2
              linarith
            have hpq_strip : [p, q] <+ strip := by
              have := hpq.filter fun p => decide ((p.1 - xmid) ^ 2 < δ)
              simpa [hpstrip, hqstrip] using this
            have hgap := sq_sub_snd_le_dist2 p q
            rcases pair_sublist_of_perm hperm.symm hpq_strip with h | h
            · exact stripScan_lower δ ys hsorted p q h (by linarith)
            · obtain ⟨d, hd, hdle⟩ := stripScan_lower δ ys hsorted q p h (by
                rw [show (p.2 - q.2) ^ 2 = (q.2 - p.2) ^ 2 by ring]; linarith)
              exact ⟨d, hd, by rwa [dist2_comm]⟩

/-! ## Correctness

## Depends on

- [Is Answer](is-answer.md)
- [Closest Pair](closest-pair.md)

## Proof depends on

- [Closest Rec](closest-rec.md)
- [Closest Rec is Answer](closest-rec-is-answer.md)
- [Dist2](dist2.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ClosestPair](../../../../../../sources/v2/CSLibExt.md)
