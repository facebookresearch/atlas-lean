/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalExternal









namespace StatMech.Onsager

open BigOperators Finset

section GenericReroot

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {n : ℕ} [NeZero n]

noncomputable def ons_invariantRerootTerm
    (weight : (Fin n → E) → ℂ) (e r : E) (loop : Fin n → E) : ℂ :=
  if (∀ j, loop j ≠ r) ∧ loop 0 = e then
    weight loop / (ons_visitCount e loop : ℂ)
  else 0

noncomputable def ons_invariantMarkedTerm
    (weight : (Fin n → E) → ℂ) (e r : E)
    (k : Fin n) (loop : Fin n → E) : ℂ :=
  if (∀ j, loop j ≠ r) ∧ loop k = e then
    weight loop / (ons_visitCount e loop : ℂ)
  else 0

theorem ons_invariantMarkedTerm_eq_rerootTerm
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) (k : Fin n) (loop : Fin n → E) :
    ons_invariantMarkedTerm weight e r k loop =
      ons_invariantRerootTerm weight e r (ons_rotate k loop) := by
  unfold ons_invariantMarkedTerm ons_invariantRerootTerm
  by_cases h : (∀ j, loop j ≠ r) ∧ loop k = e
  · rw [if_pos h]
    have hrot : (∀ j, ons_rotate k loop j ≠ r) ∧
        ons_rotate k loop 0 = e :=
      ⟨(ons_avoids_rotate r k loop).2 h.1, by simpa using h.2⟩
    rw [if_pos hrot, hrotate, ons_visitCount_rotate]
  · rw [if_neg h]
    have hrot : ¬ ((∀ j, ons_rotate k loop j ≠ r) ∧
        ons_rotate k loop 0 = e) := by
      intro hr
      apply h
      exact ⟨(ons_avoids_rotate r k loop).1 hr.1, by simpa using hr.2⟩
    rw [if_neg hrot]

theorem ons_sum_invariantMarkedTerm
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) (k : Fin n) :
    ∑ loop : Fin n → E, ons_invariantMarkedTerm weight e r k loop =
      ∑ loop : Fin n → E, ons_invariantRerootTerm weight e r loop := by
  simp_rw [ons_invariantMarkedTerm_eq_rerootTerm weight hrotate]
  exact Equiv.sum_comp (ons_rotateEquiv k)
    (ons_invariantRerootTerm weight e r)

theorem ons_sum_invariantMarks_recovers
    (weight : (Fin n → E) → ℂ) (e r : E) (loop : Fin n → E) :
    (∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
      if (∀ j, loop j ≠ r) ∧ (∃ k, loop k = e) then weight loop else 0 := by
  unfold ons_invariantMarkedTerm
  by_cases hav : ∀ j, loop j ≠ r
  · have hterm : ∀ k : Fin n,
        (if (∀ j, loop j ≠ r) ∧ loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0) =
          if loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0 := by
      intro k
      by_cases hk : loop k = e <;> simp [hav, hk]
    rw [Finset.sum_congr rfl (fun k _ ↦ hterm k)]
    by_cases hvis : ∃ k, loop k = e
    · rw [if_pos ⟨hav, hvis⟩]
      have hcount : 0 < ons_visitCount e loop :=
        (ons_visitCount_pos_iff e loop).2 hvis
      have hcountC : (ons_visitCount e loop : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcount)
      have hsum : (∑ k : Fin n, if loop k = e then (1 : ℂ) else 0) =
          (ons_visitCount e loop : ℂ) := by
        rw [Finset.sum_boole, ons_visitCount_eq_card_filter]
      calc
        (∑ k : Fin n, if loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0) =
            (∑ k : Fin n, if loop k = e then (1 : ℂ) else 0) *
              (weight loop / (ons_visitCount e loop : ℂ)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro k hk
                split_ifs <;> simp
        _ = weight loop := by
          rw [hsum]
          field_simp [hcountC]
    · rw [if_neg (fun h ↦ hvis h.2)]
      push Not at hvis
      simp [hvis]
  · have hcond : ¬ ((∀ j, loop j ≠ r) ∧ ∃ k, loop k = e) := by
      aesop
    rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    exact fun h ↦ hav h.1

theorem ons_sum_div_length_eq_rerooted_of_invariant
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) :
    (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
        (∃ k, loop k = e) ∧ ∀ j, loop j ≠ r), weight loop) / (n : ℂ) =
      ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
        loop 0 = e ∧ ∀ j, loop j ≠ r),
        weight loop / (ons_visitCount e loop : ℂ) := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  have hdouble :
      (∑ loop : Fin n → E,
        ∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
        (n : ℂ) * ∑ loop : Fin n → E,
          ons_invariantRerootTerm weight e r loop := by
    rw [Finset.sum_comm]
    simp_rw [ons_sum_invariantMarkedTerm weight hrotate]
    simp
  have hleft :
      (∑ loop : Fin n → E,
        ∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
        ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
          (∃ k, loop k = e) ∧ ∀ j, loop j ≠ r), weight loop := by
    simp_rw [ons_sum_invariantMarks_recovers]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext loop
      simp [and_comm]
    · simp
  have hright :
      (∑ loop : Fin n → E, ons_invariantRerootTerm weight e r loop) =
        ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
          loop 0 = e ∧ ∀ j, loop j ≠ r),
          weight loop / (ons_visitCount e loop : ℂ) := by
    unfold ons_invariantRerootTerm
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext loop
      simp [and_comm]
    · simp
  rw [hleft, hright] at hdouble
  apply (div_eq_iff hn).2
  simpa [mul_comm] using hdouble

end GenericReroot

theorem ons_decFixedExponentTerm_rotate
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (m : ons_DecEdge L →₀ ℕ)
    (k : Fin n) (loop : Fin n → ons_Dart L) :
    (if ons_decLoopExponent L (ons_rotate k loop) = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) (ons_rotate k loop)
      else 0) =
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0 := by
  rw [ons_decLoopExponent_rotate, ons_decLoopScalar_rotate]

theorem ons_decFormalFixedBucketE_div_eq_rerooted
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (d : ons_Dart L) (r : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1) =
      ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (r + 1) → ons_Dart L ↦
            loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d),
        (if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / (ons_visitCount d loop : ℂ) := by
  let weight : (Fin (r + 1) → ons_Dart L) → ℂ := fun loop ↦
    if ons_decLoopExponent L loop = m then
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop
    else 0
  have hreroot := ons_sum_div_length_eq_rerooted_of_invariant weight
    (fun k loop ↦ ons_decFixedExponentTerm_rotate L a b m k loop)
    d (ons_dartRev L d)
  unfold ons_decFormalFixedBucketE
  simpa only [weight, Nat.cast_add, Nat.cast_one, not_exists] using hreroot

section PathSum

variable {E M : Type*} [AddCommMonoid M]

def ons_pathSum (step : E → E → M) : List E → M
  | [] => 0
  | [_] => 0
  | x :: y :: tail => step x y + ons_pathSum step (y :: tail)

@[simp] theorem ons_pathSum_nil (step : E → E → M) :
    ons_pathSum step [] = 0 := rfl

@[simp] theorem ons_pathSum_singleton (step : E → E → M) (x : E) :
    ons_pathSum step [x] = 0 := rfl

theorem ons_pathSum_cons_cons (step : E → E → M)
    (x y : E) (tail : List E) :
    ons_pathSum step (x :: y :: tail) =
      step x y + ons_pathSum step (y :: tail) := rfl

theorem ons_pathSum_append_cons (step : E → E → M)
    (pre : List E) (x : E) (suffix : List E) :
    ons_pathSum step (pre ++ x :: suffix) =
      ons_pathSum step (pre ++ [x]) + ons_pathSum step (x :: suffix) := by
  induction pre with
  | nil => simp
  | cons a tail ih =>
      cases tail with
      | nil =>
          simp [ons_pathSum]
      | cons b tail =>
          simp only [List.cons_append, ons_pathSum_cons_cons]
          simpa only [List.cons_append, add_assoc] using
            congrArg (fun z ↦ step a b + z) ih

theorem ons_pathSum_glue (step : E → E → M) (root : E)
    (segments : List (List E))
    (hhead : ∀ segment ∈ segments, segment.head? = some root)
    (hlast : ∀ segment ∈ segments, segment.getLast? = some root) :
    ons_pathSum step (ons_glue root segments) =
      (segments.map (ons_pathSum step)).sum := by
  induction segments with
  | nil => simp [ons_glue]
  | cons segment segments ih =>
      have hsegmentHead := hhead segment (by simp)
      have hsegmentLast := hlast segment (by simp)
      have hhead' : ∀ s ∈ segments, s.head? = some root :=
        fun s hs ↦ hhead s (by simp [hs])
      have hlast' : ∀ s ∈ segments, s.getLast? = some root :=
        fun s hs ↦ hlast s (by simp [hs])
      obtain ⟨tail, htail⟩ := ons_glue_head root segments hhead'
      have hne : segment ≠ [] := by
        rintro rfl
        simp at hsegmentHead
      have hreconstruct : segment.dropLast ++ [root] = segment :=
        List.dropLast_append_getLast? root hsegmentLast
      rw [ons_glue_cons, htail,
        ons_pathSum_append_cons, ← htail, hreconstruct,
        ih hhead' hlast']
      simp

theorem ons_pathSum_ofFn (step : E → E → M) (n : ℕ)
    (f : Fin (n + 1) → E) :
    ons_pathSum step (List.ofFn f) =
      ∑ i : Fin n, step (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
      rw [List.ofFn_succ]
      let g : Fin (n + 1) → E := fun i ↦ f i.succ
      have hg : List.ofFn g = g 0 :: List.ofFn (fun i : Fin n ↦ g i.succ) := by
        rw [List.ofFn_succ]
      rw [hg, ons_pathSum_cons_cons, ← hg, ih g, Fin.sum_univ_succ]
      simp only [g, Fin.castSucc_zero, Fin.succ_castSucc]

theorem ons_cyclicSum_eq_pathSum (step : E → E → M)
    {n : ℕ} (loop : Fin (n + 1) → E) :
    (∑ k, step (loop k) (loop (k + 1))) =
      ons_pathSum step (List.ofFn loop ++ [loop 0]) := by
  have hlist : List.ofFn loop ++ [loop 0] =
      List.ofFn (Fin.snoc loop (loop 0) : Fin (n + 2) → E) := by
    rw [List.ofFn_succ' (Fin.snoc loop (loop 0) : Fin (n + 2) → E)]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hlist, ons_pathSum_ofFn]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fin.snoc_castSucc, ons_snoc_succ]

end PathSum

theorem ons_decLoopExponent_eq_pathSum
    (L : ℕ) {n : ℕ} (loop : Fin (n + 1) → ons_Dart L) :
    ons_decLoopExponent L loop =
      ons_pathSum (ons_decTransitionExponent L)
        (List.ofFn loop ++ [loop 0]) := by
  unfold ons_decLoopExponent
  exact ons_cyclicSum_eq_pathSum (ons_decTransitionExponent L) loop

theorem ons_decLoopExponent_eq_firstReturnFactors_sum
    (L : ℕ) {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L) (hroot : loop 0 = d) :
    ons_decLoopExponent L loop =
      ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map
        (ons_pathSum (ons_decTransitionExponent L))).sum := by
  let closed := List.ofFn loop ++ [d]
  have hclosed : List.ofFn loop ++ [loop 0] = closed := by
    rw [hroot]
  have hhead : closed.head? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl]
    simp [List.ofFn_succ, hroot]
  have hlast : closed.getLast? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl,
      List.getLast?_append_of_ne_nil _ (by simp : [d] ≠ [])]
    simp
  have hspec := ons_firstReturnFactors_spec d closed hhead hlast
  rw [ons_decLoopExponent_eq_pathSum, hclosed, ← hspec.2.2]
  apply ons_pathSum_glue
  · intro segment hsegment
    exact ons_firstReturnSegment_head (hspec.2.1 segment hsegment)
  · intro segment hsegment
    exact ons_firstReturnSegment_last (hspec.2.1 segment hsegment)

theorem ons_decLoopScalar_eq_firstReturnFactors_prod
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L) (hroot : loop 0 = d) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop =
      ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map
        (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)))).prod := by
  let Lambda := ons_KWmatWeightedPhase L (fun _ ↦ 1)
    ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
  let closed := List.ofFn loop ++ [d]
  have hclosed : List.ofFn loop ++ [loop 0] = closed := by
    rw [hroot]
  have hhead : closed.head? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl]
    simp [List.ofFn_succ, hroot]
  have hlast : closed.getLast? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl,
      List.getLast?_append_of_ne_nil _ (by simp : [d] ≠ [])]
    simp
  have hspec := ons_firstReturnFactors_spec d closed hhead hlast
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_loopWeight_eq_edgeWeight, hclosed, ← hspec.2.2]
  exact ons_edgeWeight_glue Lambda d _
    (fun segment hsegment ↦
      ons_firstReturnSegment_head (hspec.2.1 segment hsegment))
    (fun segment hsegment ↦
      ons_firstReturnSegment_last (hspec.2.1 segment hsegment))

theorem ons_firstReturnSegment_eq_closedFinLoop
    {E : Type*} {d : E} {segment : List E}
    (hsegment : ons_isFirstReturnSegment d segment) :
    ∃ (n : ℕ) (loop : Fin (n + 1) → E),
      loop 0 = d ∧
      (∀ k, k ≠ 0 → loop k ≠ d) ∧
      segment = List.ofFn loop ++ [d] := by
  obtain ⟨interior, hform, hinterior⟩ := hsegment
  let loop : Fin (interior.length + 1) → E :=
    (d :: interior).get
  refine ⟨interior.length, loop, ?_, ?_, ?_⟩
  · simp [loop]
  · intro k
    refine Fin.cases (motive := fun k ↦ k ≠ 0 → loop k ≠ d) ?_ ?_ k
    · intro hk
      exact (hk rfl).elim
    · intro j hk
      simpa [loop] using hinterior (interior.get j) (List.get_mem interior j)
  · rw [hform]
    have hofFn : List.ofFn loop = d :: interior := by
      exact List.ofFn_get (d :: interior)
    rw [hofFn]

theorem ons_closedFinLoop_isFirstReturnSegment
    {E : Type*} {n : ℕ} {d : E} (loop : Fin (n + 1) → E)
    (hroot : loop 0 = d)
    (hfirst : ∀ k, k ≠ 0 → loop k ≠ d) :
    ons_isFirstReturnSegment d (List.ofFn loop ++ [d]) := by
  let interior := List.ofFn (fun k : Fin n ↦ loop k.succ)
  refine ⟨interior, ?_, ?_⟩
  · rw [List.ofFn_succ]
    exact congrArg (fun x ↦ x :: interior ++ [d]) hroot
  · intro x hx
    rw [show interior = List.ofFn (fun k : Fin n ↦ loop k.succ) from rfl,
      List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact hfirst k.succ (by simp)

theorem ons_firstReturnSegment_avoids_of_closedLoop
    {L n : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) (loop : Fin (n + 1) → ons_Dart L)
    (havoid : ∀ k, loop k ≠ ons_dartRev L d) :
    ∀ x ∈ List.ofFn loop ++ [d], x ≠ ons_dartRev L d := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact havoid k
  · simp only [List.mem_singleton] at hx
    subst x
    exact (ons_dartRev_ne L d).symm

theorem ons_decFirstReturnSegment_pathSum_eq_loopExponent
    (L : ℕ) {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L)
    (hroot : loop 0 = d) :
    ons_pathSum (ons_decTransitionExponent L) (List.ofFn loop ++ [d]) =
      ons_decLoopExponent L loop := by
  rw [← hroot]
  exact (ons_decLoopExponent_eq_pathSum L loop).symm

theorem ons_decFirstReturnSegment_edgeWeight_eq_loopScalar
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L)
    (hroot : loop 0 = d) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (List.ofFn loop ++ [d]) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop := by
  rw [← hroot, ← ons_loopWeight_eq_edgeWeight,
    ons_decLoopScalar_eq_loopWeight_one]






abbrev ons_DecFirstReturnAtom
    (L : ℕ) (d : ons_Dart L) :=
  Σ n : ℕ, {loop : Fin (n + 1) → ons_Dart L //
    ons_decIsFirstReturnLoop d loop}

def ons_decFirstReturnAtomSegment
    {L : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : List (ons_Dart L) :=
  List.ofFn atom.2.1 ++ [d]

theorem ons_decFirstReturnAtomSegment_valid
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) :
    ons_isFirstReturnSegment d (ons_decFirstReturnAtomSegment atom) ∧
      ∀ x ∈ ons_decFirstReturnAtomSegment atom,
        x ≠ ons_dartRev L d := by
  rcases atom with ⟨n, loop, hloop⟩
  refine ⟨ons_closedFinLoop_isFirstReturnSegment loop hloop.1 hloop.2.1, ?_⟩
  exact ons_firstReturnSegment_avoids_of_closedLoop d loop hloop.2.2

theorem ons_decFirstReturnAtomSegment_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decFirstReturnAtomSegment :
        ons_DecFirstReturnAtom L d → List (ons_Dart L)) := by
  rintro ⟨n, loop, hloop⟩ ⟨n', loop', hloop'⟩ hsegment
  have hlength := congrArg List.length hsegment
  simp only [ons_decFirstReturnAtomSegment, List.length_append,
    List.length_ofFn, List.length_singleton] at hlength
  have hn : n = n' := by omega
  subst n'
  have hofFn : List.ofFn loop = List.ofFn loop' := by
    exact List.append_cancel_right hsegment
  have hloopEq : loop = loop' := List.ofFn_injective hofFn
  subst loop'
  rfl

theorem ons_decFirstReturnAtomSegment_surjective
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L} :
    Function.Surjective
      (fun atom : ons_DecFirstReturnAtom L d ↦
        (⟨ons_decFirstReturnAtomSegment atom,
          ons_decFirstReturnAtomSegment_valid atom⟩ :
          {segment : List (ons_Dart L) //
            ons_isFirstReturnSegment d segment ∧
              ∀ x ∈ segment, x ≠ ons_dartRev L d})) := by
  rintro ⟨segment, hfirst, havoid⟩
  obtain ⟨n, loop, hroot, hreturn, hsegment⟩ :=
    ons_firstReturnSegment_eq_closedFinLoop hfirst
  have hrev : ∀ k, loop k ≠ ons_dartRev L d := by
    intro k hk
    apply havoid (loop k)
    · rw [hsegment, List.mem_append]
      exact Or.inl (List.mem_ofFn.mpr ⟨k, rfl⟩)
    · exact hk
  let atom : ons_DecFirstReturnAtom L d :=
    ⟨n, ⟨loop, hroot, hreturn, hrev⟩⟩
  refine ⟨atom, Subtype.ext ?_⟩
  exact hsegment.symm



noncomputable def ons_decFirstReturnAtomEquivSegment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecFirstReturnAtom L d ≃
      {segment : List (ons_Dart L) //
        ons_isFirstReturnSegment d segment ∧
          ∀ x ∈ segment, x ≠ ons_dartRev L d} :=
  Equiv.ofBijective
    (fun atom ↦ ⟨ons_decFirstReturnAtomSegment atom,
      ons_decFirstReturnAtomSegment_valid atom⟩)
    ⟨fun _ _ h ↦ ons_decFirstReturnAtomSegment_injective
      (congrArg Subtype.val h),
      ons_decFirstReturnAtomSegment_surjective⟩

@[simp] theorem ons_decFirstReturnAtomEquivSegment_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    (ons_decFirstReturnAtomEquivSegment L d atom).1 =
      ons_decFirstReturnAtomSegment atom := rfl

theorem ons_decFirstReturnAtom_exponent_segment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_pathSum (ons_decTransitionExponent L)
        (ons_decFirstReturnAtomSegment atom) =
      ons_decLoopExponent L atom.2.1 := by
  exact ons_decFirstReturnSegment_pathSum_eq_loopExponent
    L d atom.2.1 atom.2.2.1

theorem ons_decFirstReturnAtom_weight_segment
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decFirstReturnAtomSegment atom) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1 := by
  exact ons_decFirstReturnSegment_edgeWeight_eq_loopScalar
    L a b d atom.2.1 atom.2.2.1

noncomputable instance ons_decFirstReturnAtom_inhabited
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    Inhabited (ons_DecFirstReturnAtom L d) := by
  let loop : Fin 1 → ons_Dart L := fun _ ↦ d
  refine ⟨⟨0, ⟨loop, ?_, ?_, ?_⟩⟩⟩
  · rfl
  · intro k hk
    exact (hk (Fin.eq_zero k)).elim
  · intro k
    exact (ons_dartRev_ne L d).symm

noncomputable def ons_decFirstReturnSegmentAtom
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segment : List (ons_Dart L)) : ons_DecFirstReturnAtom L d := by
  classical
  exact if h : ons_isFirstReturnSegment d segment ∧
        ∀ x ∈ segment, x ≠ ons_dartRev L d then
      (ons_decFirstReturnAtomEquivSegment L d).symm ⟨segment, h⟩
    else default

theorem ons_decFirstReturnSegmentAtom_segment
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segment : List (ons_Dart L))
    (hsegment : ons_isFirstReturnSegment d segment ∧
      ∀ x ∈ segment, x ≠ ons_dartRev L d) :
    ons_decFirstReturnAtomSegment
        (ons_decFirstReturnSegmentAtom L d segment) = segment := by
  unfold ons_decFirstReturnSegmentAtom
  rw [dif_pos hsegment]
  exact congrArg Subtype.val
    ((ons_decFirstReturnAtomEquivSegment L d).apply_symm_apply
      ⟨segment, hsegment⟩)

noncomputable def ons_decFirstReturnAtomsSegments
    {L : ℕ} (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    List (List (ons_Dart L)) :=
  atoms.map ons_decFirstReturnAtomSegment

theorem ons_decFirstReturnAtomsSegments_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    ons_validFactorList d (ons_dartRev L d)
      (ons_decFirstReturnAtomsSegments d atoms) := by
  intro segment hsegment
  rw [ons_decFirstReturnAtomsSegments, List.mem_map] at hsegment
  obtain ⟨atom, hatom, rfl⟩ := hsegment
  exact ons_decFirstReturnAtomSegment_valid atom

theorem ons_decFirstReturnAtomsSegments_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decFirstReturnAtomsSegments d :
        List (ons_DecFirstReturnAtom L d) →
          List (List (ons_Dart L))) := by
  exact List.map_injective_iff.mpr
    ons_decFirstReturnAtomSegment_injective

theorem ons_decFirstReturnAtomsSegments_surjective_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segments : List (List (ons_Dart L)))
    (hsegments : ons_validFactorList d (ons_dartRev L d) segments) :
    ∃ atoms : List (ons_DecFirstReturnAtom L d),
      ons_decFirstReturnAtomsSegments d atoms = segments := by
  refine ⟨segments.map (ons_decFirstReturnSegmentAtom L d), ?_⟩
  unfold ons_decFirstReturnAtomsSegments
  rw [List.map_map]
  induction segments with
  | nil => rfl
  | cons segment segments ih =>
      simp only [List.map_cons, Function.comp_apply]
      rw [ons_decFirstReturnSegmentAtom_segment L d segment
          (hsegments segment (by simp))]
      congr 1
      apply ih
      intro s hs
      exact hsegments s (by simp [hs])



noncomputable def ons_decFirstReturnAtomsEquivFactorList
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    List (ons_DecFirstReturnAtom L d) ≃
      {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} :=
  Equiv.ofBijective
    (fun atoms ↦ ⟨ons_decFirstReturnAtomsSegments d atoms,
      ons_decFirstReturnAtomsSegments_valid L d atoms⟩)
    ⟨fun _ _ h ↦ ons_decFirstReturnAtomsSegments_injective
      (congrArg Subtype.val h), by
        rintro ⟨segments, hsegments⟩
        obtain ⟨atoms, hatoms⟩ :=
          ons_decFirstReturnAtomsSegments_surjective_valid
            L d segments hsegments
        exact ⟨atoms, Subtype.ext hatoms⟩⟩

@[simp] theorem ons_decFirstReturnAtomsEquivFactorList_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    (ons_decFirstReturnAtomsEquivFactorList L d atoms).1 =
      ons_decFirstReturnAtomsSegments d atoms := rfl

abbrev ons_DecRootedAtom
    (L : ℕ) (d : ons_Dart L) :=
  Σ n : ℕ, {loop : Fin (n + 1) → ons_Dart L //
    loop 0 = d ∧ ∀ k, loop k ≠ ons_dartRev L d}

def ons_decRootedAtomList
    {L : ℕ} {d : ons_Dart L} (atom : ons_DecRootedAtom L d) :
    List (ons_Dart L) :=
  List.ofFn atom.2.1 ++ [d]

theorem ons_decRootedAtomList_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecRootedAtom L d) :
    ons_validRootedList d (ons_dartRev L d)
      (ons_decRootedAtomList atom) ∧
      2 ≤ (ons_decRootedAtomList atom).length := by
  rcases atom with ⟨n, loop, hroot, havoid⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ons_decRootedAtomList, List.ofFn_succ, hroot]
  · change (List.ofFn loop ++ [d]).getLast? = some d
    exact List.getLast?_concat
  · intro x hx
    rw [ons_decRootedAtomList, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.mem_ofFn] at hx
      obtain ⟨k, rfl⟩ := hx
      exact havoid k
    · simp only [List.mem_singleton] at hx
      subst x
      exact (ons_dartRev_ne L d).symm
  · simp [ons_decRootedAtomList]

theorem ons_decRootedAtomList_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decRootedAtomList :
        ons_DecRootedAtom L d → List (ons_Dart L)) := by
  rintro ⟨n, loop, hloop⟩ ⟨n', loop', hloop'⟩ hlist
  have hlength := congrArg List.length hlist
  simp only [ons_decRootedAtomList, List.length_append,
    List.length_ofFn, List.length_singleton] at hlength
  have hn : n = n' := by omega
  subst n'
  have hofFn : List.ofFn loop = List.ofFn loop' :=
    List.append_cancel_right hlist
  have hloopEq : loop = loop' := List.ofFn_injective hofFn
  subst loop'
  rfl

theorem ons_validRootedList_eq_closedFinLoop
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (w : List (ons_Dart L))
    (hw : ons_validRootedList d (ons_dartRev L d) w)
    (hlength : 2 ≤ w.length) :
    ∃ atom : ons_DecRootedAtom L d,
      ons_decRootedAtomList atom = w := by
  let pre := w.dropLast
  have hreconstruct : pre ++ [d] = w := by
    exact List.dropLast_append_getLast? d hw.2.1
  have hprefixLength : 0 < pre.length := by
    have hwne : w ≠ [] := by
      intro h
      rw [h] at hlength
      simp at hlength
    rw [show pre.length = w.length - 1 by
      exact List.length_dropLast]
    omega
  obtain ⟨x, xs, hprefix⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_iff_length_pos.mpr hprefixLength)
  have hx : x = d := by
    rw [← hreconstruct, hprefix] at hw
    simpa using hw.1
  subst x
  let loop : Fin (xs.length + 1) → ons_Dart L := (d :: xs).get
  have hroot : loop 0 = d := by simp [loop]
  have havoid : ∀ k, loop k ≠ ons_dartRev L d := by
    intro k
    apply hw.2.2 (loop k)
    rw [← hreconstruct, List.mem_append]
    left
    rw [hprefix]
    exact List.get_mem (d :: xs) k
  let atom : ons_DecRootedAtom L d :=
    ⟨xs.length, ⟨loop, hroot, havoid⟩⟩
  refine ⟨atom, ?_⟩
  change List.ofFn loop ++ [d] = w
  rw [List.ofFn_get (d :: xs), ← hprefix, hreconstruct]



noncomputable def ons_decRootedAtomEquivRootedList
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecRootedAtom L d ≃
      {w : List (ons_Dart L) //
        ons_validRootedList d (ons_dartRev L d) w ∧ 2 ≤ w.length} :=
  Equiv.ofBijective
    (fun atom ↦ ⟨ons_decRootedAtomList atom,
      ons_decRootedAtomList_valid L d atom⟩)
    ⟨fun _ _ h ↦ ons_decRootedAtomList_injective
      (congrArg Subtype.val h), by
        rintro ⟨w, hw, hlength⟩
        obtain ⟨atom, hatom⟩ :=
          ons_validRootedList_eq_closedFinLoop w hw hlength
        exact ⟨atom, Subtype.ext hatom⟩⟩

@[simp] theorem ons_decRootedAtomEquivRootedList_apply_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecRootedAtom L d) :
    (ons_decRootedAtomEquivRootedList L d atom).1 =
      ons_decRootedAtomList atom := rfl

theorem ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton
    {E : Type*} [DecidableEq E] (e r : E)
    (w : List E) (hw : ons_validRootedList e r w) :
    ons_firstReturnFactors e w = [] ↔ w = [e] := by
  constructor
  · intro hfactors
    have hspec := ons_firstReturnFactors_spec e w hw.1 hw.2.1
    rw [← hspec.2.2, hfactors]
    rfl
  · rintro rfl
    simp [ons_firstReturnFactors, ons_firstReturnSplit]

theorem ons_rootedList_nontrivial_iff_factors_ne_nil
    {E : Type*} [DecidableEq E] (e r : E)
    (w : List E) (hw : ons_validRootedList e r w) :
    2 ≤ w.length ↔ ons_firstReturnFactors e w ≠ [] := by
  rw [ne_eq, ons_firstReturnFactors_eq_nil_iff_rooted_eq_singleton e r w hw]
  constructor
  · intro hlength hwone
    rw [hwone] at hlength
    simp at hlength
  · intro hwone
    have hpos : 0 < w.length := by
      apply List.length_pos_iff.mpr
      intro hwempty
      have hhead := hw.1
      rw [hwempty] at hhead
      simp at hhead
    by_contra hlength
    have hone : w.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
    apply hwone
    rw [hx] at hw ⊢
    simpa using hw.1



noncomputable def ons_decNontrivialRootedEquivNonemptyFactors
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    {w : {w : List (ons_Dart L) //
        ons_validRootedList d (ons_dartRev L d) w} //
      2 ≤ w.1.length} ≃
    {segments : {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} //
      segments.1 ≠ []} :=
  Equiv.subtypeEquiv
    (ons_rootedFactorEquiv d (ons_dartRev L d)
      (ons_dartRev_ne L d).symm)
    (fun w ↦ ons_rootedList_nontrivial_iff_factors_ne_nil
      d (ons_dartRev L d) w.1 w.2)

noncomputable def ons_decNonemptyAtomsEquivNonemptyFactors
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    {atoms : List (ons_DecFirstReturnAtom L d) // atoms ≠ []} ≃
    {segments : {segments : List (List (ons_Dart L)) //
        ons_validFactorList d (ons_dartRev L d) segments} //
      segments.1 ≠ []} :=
  Equiv.subtypeEquiv
    (ons_decFirstReturnAtomsEquivFactorList L d)
    (fun atoms ↦ by
      rw [ons_decFirstReturnAtomsEquivFactorList_apply_val]
      unfold ons_decFirstReturnAtomsSegments
      simp)



noncomputable def ons_decRootedAtomEquivNonemptyAtoms
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    ons_DecRootedAtom L d ≃
      {atoms : List (ons_DecFirstReturnAtom L d) // atoms ≠ []} :=
  (ons_decRootedAtomEquivRootedList L d).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (ons_validRootedList d (ons_dartRev L d))
      (fun w ↦ 2 ≤ w.length)).symm |>.trans <|
    (ons_decNontrivialRootedEquivNonemptyFactors L d).trans
      (ons_decNonemptyAtomsEquivNonemptyFactors L d).symm

theorem ons_decRootedAtomEquivNonemptyAtoms_segments
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decFirstReturnAtomsSegments d
        (ons_decRootedAtomEquivNonemptyAtoms L d root).1 =
      ons_firstReturnFactors d (ons_decRootedAtomList root) := by
  let rooted :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (ons_validRootedList d (ons_dartRev L d))
      (fun w ↦ 2 ≤ w.length)).symm
      (ons_decRootedAtomEquivRootedList L d root)
  let factors := ons_decNontrivialRootedEquivNonemptyFactors L d rooted
  let atoms :=
    (ons_decNonemptyAtomsEquivNonemptyFactors L d).symm factors
  have hatoms := congrArg (fun z ↦ z.1.1)
    ((ons_decNonemptyAtomsEquivNonemptyFactors L d).apply_symm_apply factors)
  change ons_decFirstReturnAtomsSegments d atoms.1 = factors.1.1 at hatoms
  change ons_decFirstReturnAtomsSegments d atoms.1 =
    ons_firstReturnFactors d (ons_decRootedAtomList root)
  exact hatoms

noncomputable def ons_decFirstReturnAtomExponent
    {L : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L atom.2.1

noncomputable def ons_decFirstReturnAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1

noncomputable def ons_decRootedAtomExponent
    {L : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtom L d) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L root.2.1

noncomputable def ons_decRootedAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L}
    (root : ons_DecRootedAtom L d) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) root.2.1

theorem ons_decRootedAtomExponent_eq_atoms_sum
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomExponent root =
      ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map
        ons_decFirstReturnAtomExponent).sum := by
  have hexponent := ons_decLoopExponent_eq_firstReturnFactors_sum
    L d root.2.1 root.2.2.1
  change ons_decRootedAtomExponent root =
      ((ons_firstReturnFactors d (ons_decRootedAtomList root)).map
        (ons_pathSum (ons_decTransitionExponent L))).sum at hexponent
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hexponent
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root).1
  have hmap :
      atoms.map
          (ons_pathSum (ons_decTransitionExponent L) ∘
            ons_decFirstReturnAtomSegment) =
        atoms.map ons_decFirstReturnAtomExponent := by
    apply List.map_congr_left
    intro atom hatom
    exact ons_decFirstReturnAtom_exponent_segment L d atom
  simp only [ons_decFirstReturnAtomsSegments, List.map_map] at hexponent
  dsimp only [atoms] at hmap
  rw [hmap] at hexponent
  exact hexponent

theorem ons_decRootedAtomWeight_eq_atoms_prod
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomWeight L a b root =
      ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map
        (ons_decFirstReturnAtomWeight L a b)).prod := by
  have hweight := ons_decLoopScalar_eq_firstReturnFactors_prod
    L a b d root.2.1 root.2.2.1
  change ons_decRootedAtomWeight L a b root =
      ((ons_firstReturnFactors d (ons_decRootedAtomList root)).map
        (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)))).prod
    at hweight
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hweight
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root).1
  have hmap :
      atoms.map
          (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) ∘
            ons_decFirstReturnAtomSegment) =
        atoms.map (ons_decFirstReturnAtomWeight L a b) := by
    apply List.map_congr_left
    intro atom hatom
    exact ons_decFirstReturnAtom_weight_segment L a b d atom
  simp only [ons_decFirstReturnAtomsSegments, List.map_map] at hweight
  dsimp only [atoms] at hmap
  rw [hmap] at hweight
  exact hweight

theorem ons_decRootedAtom_atoms_length_eq_visitCount
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    (ons_decRootedAtomEquivNonemptyAtoms L d root).1.length =
      ons_visitCount d root.2.1 := by
  have hlength := ons_firstReturnFactors_length
    d root.2.1 root.2.2.1
  change (ons_firstReturnFactors d
      (ons_decRootedAtomList root)).length =
    ons_visitCount d root.2.1 at hlength
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hlength
  simpa only [ons_decFirstReturnAtomsSegments, List.length_map]
    using hlength

theorem ons_decRootedAtom_externalExponent_eq_visitCount
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomExponent root s(d, ons_dartRev L d) =
      ons_visitCount d root.2.1 := by
  rw [ons_decRootedAtomExponent,
    ons_decLoopExponent_external_apply,
    ons_visitCount_eq_card_filter]
  have hterm : ∀ k,
      (if root.2.1 k = d ∨ root.2.1 k = ons_dartRev L d then 1 else 0) =
        if root.2.1 k = d then 1 else 0 := by
    intro k
    by_cases hk : root.2.1 k = d
    · simp [hk]
    · simp [hk, root.2.2.2 k]
  simp_rw [hterm]
  rw [Finset.sum_boole]
  simp

abbrev ons_DecFirstReturnAtomBounded
    (L : ℕ) (d : ons_Dart L) (N : ℕ) :=
  Σ r : Fin N, {loop : Fin (r.val + 1) → ons_Dart L //
    ons_decIsFirstReturnLoop d loop}

noncomputable def ons_decBoundedAtomExponent
    {L N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L atom.2.1

noncomputable def ons_decBoundedAtomWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {d : ons_Dart L} {N : ℕ}
    (atom : ons_DecFirstReturnAtomBounded L d N) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) atom.2.1

theorem ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalFirstReturnCoeff L a b d m =
      ∑ atom : ons_DecFirstReturnAtomBounded L d
          (ons_finsuppTotalDegree m),
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnCoeff
  rw [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro rf hrf
  change (∑ loop : Fin (rf.val + 1) → ons_Dart L,
      if ons_decIsFirstReturnLoop d loop ∧
          ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) =
    ∑ loop : {loop : Fin (rf.val + 1) → ons_Dart L //
        ons_decIsFirstReturnLoop d loop},
      if ons_decLoopExponent L loop.1 = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop.1
      else 0
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter (ons_decIsFirstReturnLoop d))
    (by simp)
    (fun loop : Fin (rf.val + 1) → ons_Dart L ↦
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro loop hloop
  by_cases hfirst : ons_decIsFirstReturnLoop d loop
  · simp [hfirst]
  · simp [hfirst]

def ons_decBoundedAtomEmbedding
    {L M N : ℕ} {d : ons_Dart L} (hMN : M ≤ N) :
    ons_DecFirstReturnAtomBounded L d M ↪
      ons_DecFirstReturnAtomBounded L d N :=
  Function.Embedding.sigmaMap (Fin.castLEEmb hMN)
    (fun _ ↦ Function.Embedding.refl _)

theorem ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (N : ℕ)
    (hdegree : ons_finsuppTotalDegree m ≤ N) :
    ons_decFormalFirstReturnCoeff L a b d m =
      ∑ atom : ons_DecFirstReturnAtomBounded L d N,
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  rw [ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms]
  let embedding := ons_decBoundedAtomEmbedding
    (L := L) (d := d) hdegree
  let term : ons_DecFirstReturnAtomBounded L d N → ℂ :=
    fun atom ↦ if ons_decBoundedAtomExponent atom = m then
      ons_decBoundedAtomWeight L a b atom else 0
  calc
    (∑ atom : ons_DecFirstReturnAtomBounded L d
        (ons_finsuppTotalDegree m),
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom else 0) =
        ∑ atom ∈ Finset.univ.map embedding, term atom := by
          rw [Finset.sum_map]
          rfl
    _ = ∑ atom : ons_DecFirstReturnAtomBounded L d N, term atom := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro atom hatom hnot
      by_cases hexponent : ons_decBoundedAtomExponent atom = m
      · exfalso
        apply hnot
        rw [Finset.mem_map]
        have hlength := ons_decLoopExponent_length_le L atom.2.1
        change atom.1.val + 1 ≤
          ons_finsuppTotalDegree (ons_decBoundedAtomExponent atom) at hlength
        rw [hexponent] at hlength
        let rsmall : Fin (ons_finsuppTotalDegree m) :=
          ⟨atom.1.val, by omega⟩
        let small : ons_DecFirstReturnAtomBounded L d
            (ons_finsuppTotalDegree m) :=
          ⟨rsmall, atom.2⟩
        refine ⟨small, Finset.mem_univ _, ?_⟩
        apply Sigma.ext
        · exact Fin.ext rfl
        · rfl
      · simp [term, hexponent]
    _ = _ := rfl

noncomputable def ons_decFormalFirstReturnTrunc
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N : ℕ) : MvPowerSeries (ons_DecEdge L) ℂ :=
  ∑ atom : ons_DecFirstReturnAtomBounded L d N,
    MvPowerSeries.monomial (ons_decBoundedAtomExponent atom)
      (ons_decBoundedAtomWeight L a b atom)

theorem ons_decFormalFirstReturnTrunc_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N) =
      ∑ atom : ons_DecFirstReturnAtomBounded L d N,
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnTrunc
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro atom hatom
  rw [MvPowerSeries.coeff_monomial]
  by_cases h : ons_decBoundedAtomExponent atom = m
  · subst m
    simp
  · simp [h, Ne.symm h]

theorem ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (N : ℕ)
    (hdegree : ons_finsuppTotalDegree m ≤ N) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d) =
      MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N) := by
  rw [ons_decFormalFirstReturnTrunc_coeff]
  exact ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le
    L a b d m N hdegree

theorem ons_finsuppTotalDegree_mono
    {E : Type*} [DecidableEq E] {m n : E →₀ ℕ} (h : m ≤ n) :
    ons_finsuppTotalDegree m ≤ ons_finsuppTotalDegree n := by
  unfold ons_finsuppTotalDegree
  exact Finsupp.sum_le_sum_index h
    (fun _ _ ↦ monotone_id) (fun _ _ ↦ rfl)

theorem ons_decFormalFirstReturn_coeff_pow_eq_trunc
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) =
      MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d
          (ons_finsuppTotalDegree m) ^ k) := by
  classical
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro exponents hexponents
  apply Finset.prod_congr rfl
  intro i hi
  apply ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le
  apply ons_finsuppTotalDegree_mono
  have hsum := (Finset.mem_finsuppAntidiag.mp hexponents).1
  rw [← hsum]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) hi

theorem ons_decFormalFirstReturnTrunc_coeff_pow
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N k : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N ^ k) =
      ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d N,
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnTrunc
  rw [Fintype.sum_pow, map_sum]
  apply Finset.sum_congr rfl
  intro atoms hatoms
  have hprod :
      (∏ i,
        MvPowerSeries.monomial (ons_decBoundedAtomExponent (atoms i))
          (ons_decBoundedAtomWeight L a b (atoms i))) =
        MvPowerSeries.monomial
          (∑ i, ons_decBoundedAtomExponent (atoms i))
          (∏ i, ons_decBoundedAtomWeight L a b (atoms i)) := by
    simpa using MvPowerSeries.prod_monomial
      (fun i : Fin k ↦ ons_decBoundedAtomExponent (atoms i))
      (fun i : Fin k ↦ ons_decBoundedAtomWeight L a b (atoms i))
      (Finset.univ : Finset (Fin k))
  rw [hprod, MvPowerSeries.coeff_monomial]
  by_cases h : (∑ i, ons_decBoundedAtomExponent (atoms i)) = m
  · subst m
    simp
  · simp [h, Ne.symm h]

theorem ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) =
      ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d
          (ons_finsuppTotalDegree m),
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0 := by
  rw [ons_decFormalFirstReturn_coeff_pow_eq_trunc,
    ons_decFormalFirstReturnTrunc_coeff_pow]

noncomputable def ons_listLengthEquivTuple
    {A : Type*} (k : ℕ) :
    {l : List A // l.length = k} ≃ (Fin k → A) where
  toFun l i := l.1.get (Fin.cast l.2.symm i)
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv := by
    rintro ⟨l, hl⟩
    apply Subtype.ext
    subst k
    exact List.ofFn_get l
  right_inv := by
    intro f
    funext i
    simp only [List.get_ofFn]
    apply congrArg f
    apply Fin.ext
    rfl

theorem ons_decFirstReturnAtom_externalExponent
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecFirstReturnAtom L d) :
    ons_decFirstReturnAtomExponent atom s(d, ons_dartRev L d) = 1 :=
  ons_decLoopExponent_external_eq_one_of_firstReturn
    L d atom.2.1 atom.2.2

theorem ons_decFirstReturnAtoms_externalExponent_sum
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    (atoms.map ons_decFirstReturnAtomExponent).sum
        s(d, ons_dartRev L d) = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, Finsupp.add_apply,
        List.length_cons, ih, ons_decFirstReturnAtom_externalExponent]
      omega

noncomputable def ons_decRootedExponentEquivAtomLists
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms ≠ [] ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} :=
  (Equiv.subtypeEquiv
    (ons_decRootedAtomEquivNonemptyAtoms L d)
    (fun root ↦ by
      rw [ons_decRootedAtomExponent_eq_atoms_sum])).trans <|
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun atoms : List (ons_DecFirstReturnAtom L d) ↦ atoms ≠ [])
      (fun atoms ↦ (atoms.map ons_decFirstReturnAtomExponent).sum = m)

noncomputable def ons_decAtomListsExponentEquivLength
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms ≠ [] ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} ≃
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d) ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} :=
  Equiv.subtypeEquiv (Equiv.refl _)
    (fun atoms ↦ by
      constructor
      · rintro ⟨hne, hexponent⟩
        refine ⟨?_, hexponent⟩
        change atoms.length = m s(d, ons_dartRev L d)
        rw [← ons_decFirstReturnAtoms_externalExponent_sum L d atoms,
          hexponent]
      · rintro ⟨hlength, hexponent⟩
        refine ⟨?_, hexponent⟩
        intro hempty
        rw [hempty] at hlength
        simp at hlength
        omega)

noncomputable def ons_decAtomListsLengthEquivTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d) ∧
        (atoms.map ons_decFirstReturnAtomExponent).sum = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun atoms : List (ons_DecFirstReturnAtom L d) ↦
        atoms.length = m s(d, ons_dartRev L d))
      (fun atoms ↦
        (atoms.map ons_decFirstReturnAtomExponent).sum = m)).symm |>.trans <|
    Equiv.subtypeEquiv
      (ons_listLengthEquivTuple (A := ons_DecFirstReturnAtom L d)
        (m s(d, ons_dartRev L d)))
      (fun atoms ↦ by
        let equiv := ons_listLengthEquivTuple
          (A := ons_DecFirstReturnAtom L d)
          (m s(d, ons_dartRev L d))
        have hlist := congrArg Subtype.val (equiv.symm_apply_apply atoms)
        change List.ofFn (equiv atoms) = atoms.1 at hlist
        change (atoms.1.map ons_decFirstReturnAtomExponent).sum = m ↔
          (∑ i, ons_decFirstReturnAtomExponent (equiv atoms i)) = m
        rw [← hlist, List.map_ofFn, List.sum_ofFn]
        rfl)

noncomputable def ons_decRootedExponentEquivUnboundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  (ons_decRootedExponentEquivAtomLists L d m).trans <|
    (ons_decAtomListsExponentEquivLength L d m hk).trans
      (ons_decAtomListsLengthEquivTuples L d m)

def ons_decForgetBoundedAtom
    {L N : ℕ} {d : ons_Dart L} :
    ons_DecFirstReturnAtomBounded L d N ↪
      ons_DecFirstReturnAtom L d :=
  Function.Embedding.sigmaMap Fin.valEmbedding
    (fun _ ↦ Function.Embedding.refl _)

@[simp] theorem ons_decForgetBoundedAtom_exponent
    {L N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decFirstReturnAtomExponent (ons_decForgetBoundedAtom atom) =
      ons_decBoundedAtomExponent atom := rfl

@[simp] theorem ons_decForgetBoundedAtom_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decFirstReturnAtomWeight L a b (ons_decForgetBoundedAtom atom) =
      ons_decBoundedAtomWeight L a b atom := rfl

noncomputable def ons_decBoundedTupleToUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} →
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  fun atoms ↦ ⟨fun i ↦ ons_decForgetBoundedAtom (atoms.1 i), by
    simpa using atoms.2⟩

theorem ons_decBoundedTupleToUnbounded_bijective
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    Function.Bijective (ons_decBoundedTupleToUnbounded L d m) := by
  classical
  constructor
  · intro atoms atoms' h
    apply Subtype.ext
    funext i
    apply ons_decForgetBoundedAtom.injective
    exact congrFun (congrArg Subtype.val h) i
  · rintro ⟨atoms, hexponent⟩
    have hbound : ∀ i,
        (atoms i).1 + 1 ≤ ons_finsuppTotalDegree m := by
      intro i
      have hcomponent : ons_decFirstReturnAtomExponent (atoms i) ≤ m := by
        rw [← hexponent]
        exact Finset.single_le_sum (fun j _ ↦
          (zero_le : (0 : ons_DecEdge L →₀ ℕ) ≤
            ons_decFirstReturnAtomExponent (atoms j)))
          (Finset.mem_univ i)
      have hdegree := ons_finsuppTotalDegree_mono hcomponent
      have hlength := ons_decLoopExponent_length_le L (atoms i).2.1
      change (atoms i).1 + 1 ≤
        ons_finsuppTotalDegree
          (ons_decFirstReturnAtomExponent (atoms i)) at hlength
      exact hlength.trans hdegree
    let bounded : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) :=
      fun i ↦ ⟨⟨(atoms i).1, by have := hbound i; omega⟩, (atoms i).2⟩
    have hbounded :
        (∑ i, ons_decBoundedAtomExponent (bounded i)) = m := by
      simpa only [bounded, ons_decBoundedAtomExponent,
        ons_decFirstReturnAtomExponent] using hexponent
    refine ⟨⟨bounded, hbounded⟩, ?_⟩
    apply Subtype.ext
    funext i
    rfl

noncomputable def ons_decBoundedTupleEquivUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtom L d //
      (∑ i, ons_decFirstReturnAtomExponent (atoms i)) = m} :=
  Equiv.ofBijective (ons_decBoundedTupleToUnbounded L d m)
    (ons_decBoundedTupleToUnbounded_bijective L d m)

noncomputable def ons_decRootedExponentEquivBoundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} :=
  (ons_decRootedExponentEquivUnboundedTuples L d m hk).trans
    (ons_decBoundedTupleEquivUnbounded L d m).symm

abbrev ons_DecRootedAtomBounded
    (L : ℕ) (d : ons_Dart L) (N : ℕ) :=
  Σ r : Fin N, {loop : Fin (r.val + 1) → ons_Dart L //
    loop 0 = d ∧ ∀ k, loop k ≠ ons_dartRev L d}

noncomputable def ons_decBoundedRootExponent
    {L N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) : ons_DecEdge L →₀ ℕ :=
  ons_decLoopExponent L root.2.1

noncomputable def ons_decBoundedRootWeight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) : ℂ :=
  ons_decLoopScalar L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) root.2.1

def ons_decForgetBoundedRoot
    {L N : ℕ} {d : ons_Dart L} :
    ons_DecRootedAtomBounded L d N ↪ ons_DecRootedAtom L d :=
  Function.Embedding.sigmaMap Fin.valEmbedding
    (fun _ ↦ Function.Embedding.refl _)

@[simp] theorem ons_decForgetBoundedRoot_exponent
    {L N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) :
    ons_decRootedAtomExponent (ons_decForgetBoundedRoot root) =
      ons_decBoundedRootExponent root := rfl

@[simp] theorem ons_decForgetBoundedRoot_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) {N : ℕ} {d : ons_Dart L}
    (root : ons_DecRootedAtomBounded L d N) :
    ons_decRootedAtomWeight L a b (ons_decForgetBoundedRoot root) =
      ons_decBoundedRootWeight L a b root := rfl

noncomputable def ons_decBoundedRootToUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} →
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} :=
  fun root ↦ ⟨ons_decForgetBoundedRoot root.1, by simpa using root.2⟩

theorem ons_decBoundedRootToUnbounded_bijective
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    Function.Bijective (ons_decBoundedRootToUnbounded L d m) := by
  classical
  constructor
  · intro root root' h
    apply Subtype.ext
    apply ons_decForgetBoundedRoot.injective
    exact congrArg Subtype.val h
  · rintro ⟨root, hexponent⟩
    have hlength := ons_decLoopExponent_length_le L root.2.1
    change root.1 + 1 ≤
      ons_finsuppTotalDegree (ons_decRootedAtomExponent root) at hlength
    rw [hexponent] at hlength
    let bounded : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m) :=
      ⟨⟨root.1, by omega⟩, root.2⟩
    have hbounded : ons_decBoundedRootExponent bounded = m := by
      simpa only [bounded, ons_decBoundedRootExponent,
        ons_decRootedAtomExponent] using hexponent
    refine ⟨⟨bounded, hbounded⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def ons_decBoundedRootEquivUnbounded
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} ≃
    {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m} :=
  Equiv.ofBijective (ons_decBoundedRootToUnbounded L d m)
    (ons_decBoundedRootToUnbounded_bijective L d m)

noncomputable def ons_decBoundedRootEquivBoundedTuples
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    {root : ons_DecRootedAtomBounded L d (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m} ≃
    {atoms : Fin (m s(d, ons_dartRev L d)) →
        ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
      (∑ i, ons_decBoundedAtomExponent (atoms i)) = m} :=
  (ons_decBoundedRootEquivUnbounded L d m).trans
    (ons_decRootedExponentEquivBoundedTuples L d m hk)

theorem ons_decFormalRootedLogCoeff_eq_boundedRootSum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalRootedLogCoeff L a b d m =
      -(∑ root : ons_DecRootedAtomBounded L d
          (ons_finsuppTotalDegree m),
        if ons_decBoundedRootExponent root = m then
          ons_decBoundedRootWeight L a b root /
            (ons_visitCount d root.2.1 : ℂ)
        else 0) := by
  classical
  unfold ons_decFormalRootedLogCoeff
  apply congrArg Neg.neg
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  rw [ons_decFormalFixedBucketE_div_eq_rerooted]
  change (∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (r.val + 1) → ons_Dart L ↦
        loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d),
      (if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
       else 0) / (ons_visitCount d loop : ℂ)) =
    ∑ loop : {loop : Fin (r.val + 1) → ons_Dart L //
        loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d},
      if ons_decLoopExponent L loop.1 = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop.1 /
            (ons_visitCount d loop.1 : ℂ)
      else 0
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter (fun loop : Fin (r.val + 1) → ons_Dart L ↦
      loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d))
    (by simp)
    (fun loop : Fin (r.val + 1) → ons_Dart L ↦
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop /
            (ons_visitCount d loop : ℂ)
      else 0)]
  rw [Finset.sum_filter]
  rw [Finset.sum_ite]
  simp
  apply Finset.sum_congr rfl
  intro loop hloop
  by_cases hexponent : ons_decLoopExponent L loop = m
  · simp [hexponent]
  · simp [hexponent]

theorem ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hzero : m s(d, ons_dartRev L d) = 0) :
    ons_decFormalRootedLogCoeff L a b d m = 0 := by
  rw [ons_decFormalRootedLogCoeff_eq_boundedRootSum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro root hroot
  rw [if_neg]
  intro hexponent
  have hvisit := ons_decRootedAtom_externalExponent_eq_visitCount
    L d (ons_decForgetBoundedRoot root)
  rw [ons_decForgetBoundedRoot_exponent, hexponent, hzero] at hvisit
  change 0 = ons_visitCount d root.2.1 at hvisit
  have hpos : 0 < ons_visitCount d root.2.1 :=
    (ons_visitCount_pos_iff d root.2.1).2 ⟨0, root.2.2.1⟩
  exact (Nat.ne_of_gt hpos) hvisit.symm

theorem ons_decRootedExponentEquivUnboundedTuples_weight
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d))
    (root : {root : ons_DecRootedAtom L d //
      ons_decRootedAtomExponent root = m}) :
    ons_decRootedAtomWeight L a b root.1 =
      ∏ i, ons_decFirstReturnAtomWeight L a b
        ((ons_decRootedExponentEquivUnboundedTuples L d m hk root).1 i) := by
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root.1).1
  let tuple :=
    (ons_decRootedExponentEquivUnboundedTuples L d m hk root).1
  have hlength : atoms.length = m s(d, ons_dartRev L d) := by
    rw [ons_decRootedAtom_atoms_length_eq_visitCount L d root.1,
      ← ons_decRootedAtom_externalExponent_eq_visitCount L d root.1,
      root.2]
  let atomVector : {atoms : List (ons_DecFirstReturnAtom L d) //
      atoms.length = m s(d, ons_dartRev L d)} := ⟨atoms, hlength⟩
  have htuple : tuple =
      ons_listLengthEquivTuple (m s(d, ons_dartRev L d)) atomVector := by
    rfl
  have hlist : List.ofFn tuple = atoms := by
    rw [htuple]
    exact congrArg Subtype.val
      ((ons_listLengthEquivTuple (m s(d, ons_dartRev L d))).symm_apply_apply
        atomVector)
  rw [ons_decRootedAtomWeight_eq_atoms_prod]
  change (atoms.map (ons_decFirstReturnAtomWeight L a b)).prod = _
  rw [← hlist, List.map_ofFn, List.prod_ofFn]
  rfl

theorem ons_decBoundedRootEquivBoundedTuples_weight_div
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d))
    (root : {root : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m) //
      ons_decBoundedRootExponent root = m}) :
    ons_decBoundedRootWeight L a b root.1 /
        (ons_visitCount d root.1.2.1 : ℂ) =
      (∏ i, ons_decBoundedAtomWeight L a b
        ((ons_decBoundedRootEquivBoundedTuples L d m hk root).1 i)) /
          (m s(d, ons_dartRev L d) : ℂ) := by
  let unboundedRoot := ons_decBoundedRootEquivUnbounded L d m root
  let unboundedTuple :=
    ons_decRootedExponentEquivUnboundedTuples L d m hk unboundedRoot
  let boundedTuple :=
    ons_decBoundedRootEquivBoundedTuples L d m hk root
  have htupleSubtype :=
    (ons_decBoundedTupleEquivUnbounded L d m).apply_symm_apply
      unboundedTuple
  have htuple :
      (∀ i, ons_decForgetBoundedAtom (boundedTuple.1 i) =
        unboundedTuple.1 i) := by
    intro i
    exact congrFun (congrArg Subtype.val htupleSubtype) i
  have hweight := ons_decRootedExponentEquivUnboundedTuples_weight
    L a b d m hk unboundedRoot
  have hweight' : ons_decBoundedRootWeight L a b root.1 =
      ∏ i, ons_decBoundedAtomWeight L a b (boundedTuple.1 i) := by
    change ons_decRootedAtomWeight L a b unboundedRoot.1 = _
    rw [hweight]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← htuple i, ons_decForgetBoundedAtom_weight]
  have hvisit := ons_decRootedAtom_externalExponent_eq_visitCount
    L d unboundedRoot.1
  have hvisit' : ons_visitCount d root.1.2.1 =
      m s(d, ons_dartRev L d) := by
    change ons_decBoundedRootExponent root.1 s(d, ons_dartRev L d) =
      ons_visitCount d root.1.2.1 at hvisit
    rw [root.2] at hvisit
    exact hvisit.symm
  rw [hweight', hvisit']

theorem ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hk : 0 < m s(d, ons_dartRev L d)) :
    ons_decFormalRootedLogCoeff L a b d m =
      -(MvPowerSeries.coeff m
          (ons_decFormalFirstReturn L a b d ^
            m s(d, ons_dartRev L d)) /
        (m s(d, ons_dartRev L d) : ℂ)) := by
  classical
  rw [ons_decFormalRootedLogCoeff_eq_boundedRootSum,
    ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum]
  apply congrArg Neg.neg
  let rootEquiv := ons_decBoundedRootEquivBoundedTuples L d m hk
  calc
    (∑ root : ons_DecRootedAtomBounded L d
        (ons_finsuppTotalDegree m),
      if ons_decBoundedRootExponent root = m then
        ons_decBoundedRootWeight L a b root /
          (ons_visitCount d root.2.1 : ℂ)
      else 0) =
      ∑ root : {root : ons_DecRootedAtomBounded L d
          (ons_finsuppTotalDegree m) //
        ons_decBoundedRootExponent root = m},
        ons_decBoundedRootWeight L a b root.1 /
          (ons_visitCount d root.1.2.1 : ℂ) := by
            rw [← Finset.sum_subtype
              (s := Finset.univ.filter
                (fun root : ons_DecRootedAtomBounded L d
                    (ons_finsuppTotalDegree m) ↦
                  ons_decBoundedRootExponent root = m))
              (by simp)
              (fun root ↦ ons_decBoundedRootWeight L a b root /
                (ons_visitCount d root.2.1 : ℂ)),
              Finset.sum_filter]
    _ = ∑ atoms : {atoms : Fin (m s(d, ons_dartRev L d)) →
          ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m) //
        (∑ i, ons_decBoundedAtomExponent (atoms i)) = m},
        (∏ i, ons_decBoundedAtomWeight L a b (atoms.1 i)) /
          (m s(d, ons_dartRev L d) : ℂ) := by
            apply Fintype.sum_equiv rootEquiv
            intro root
            exact ons_decBoundedRootEquivBoundedTuples_weight_div
              L a b d m hk root
    _ = (∑ atoms : Fin (m s(d, ons_dartRev L d)) →
          ons_DecFirstReturnAtomBounded L d (ons_finsuppTotalDegree m),
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0) / (m s(d, ons_dartRev L d) : ℂ) := by
            rw [← Finset.sum_div]
            apply congrArg (fun z : ℂ ↦
              z / (m s(d, ons_dartRev L d) : ℂ))
            rw [← Finset.sum_subtype
              (s := Finset.univ.filter
                (fun atoms : Fin (m s(d, ons_dartRev L d)) →
                    ons_DecFirstReturnAtomBounded L d
                      (ons_finsuppTotalDegree m) ↦
                  (∑ i, ons_decBoundedAtomExponent (atoms i)) = m))
              (by simp)
              (fun atoms ↦
                ∏ i, ons_decBoundedAtomWeight L a b (atoms i)),
              Finset.sum_filter]

theorem ons_decBoundedAtom_externalExponent
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) {N : ℕ}
    (atom : ons_DecFirstReturnAtomBounded L d N) :
    ons_decBoundedAtomExponent atom s(d, ons_dartRev L d) = 1 :=
  ons_decLoopExponent_external_eq_one_of_firstReturn
    L d atom.2.1 atom.2.2

theorem ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ)
    (hne : k ≠ m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) = 0 := by
  classical
  rw [ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum]
  apply Finset.sum_eq_zero
  intro atoms hatoms
  rw [if_neg]
  intro hexponent
  apply hne
  have happ := congrArg
    (fun exponent : ons_DecEdge L →₀ ℕ ↦
      exponent s(d, ons_dartRev L d)) hexponent
  simp only [Finsupp.finsetSum_apply,
    ons_decBoundedAtom_externalExponent] at happ
  simpa using happ

theorem ons_decFormalFirstReturn_neg_coeff_pow
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m ((-ons_decFormalFirstReturn L a b d) ^ k) =
      (-1 : ℂ) ^ k *
        MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) := by
  rw [show -ons_decFormalFirstReturn L a b d =
      (-1 : ℂ) • ons_decFormalFirstReturn L a b d by simp,
    smul_pow, MvPowerSeries.coeff_smul]

theorem ons_decFormalFirstReturn_neg_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (-ons_decFormalFirstReturn L a b d) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [map_neg, ons_decFormalFirstReturn_constantCoeff]
  simp

theorem ons_decFormalRootedLogCoeff_eq_log_subst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalRootedLogCoeff L a b d m =
      MvPowerSeries.coeff m
        (PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
          (PowerSeries.log ℂ)) := by
  classical
  rw [PowerSeries.coeff_subst
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  let k := m s(d, ons_dartRev L d)
  by_cases hk : k = 0
  · have hroot := ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
      L a b d m hk
    rw [hroot]
    rw [← finsum_zero]
    apply finsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      rw [PowerSeries.coeff_log]
      simp
    · have hne : n ≠ m s(d, ons_dartRev L d) := by
        change n ≠ k
        rw [hk]
        exact hn
      rw [ons_decFormalFirstReturn_neg_coeff_pow,
        ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
          L a b d m n hne, mul_zero, smul_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [finsum_eq_single _ k]
    · rw [ons_decFormalRootedLogCoeff_eq_neg_coeff_pow_div
          L a b d m hkpos,
        PowerSeries.coeff_log, if_neg hk,
        ons_decFormalFirstReturn_neg_coeff_pow]
      change -(MvPowerSeries.coeff m
          (ons_decFormalFirstReturn L a b d ^ k) / (k : ℂ)) =
        (algebraMap ℚ ℂ) ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) •
          ((-1 : ℂ) ^ k * MvPowerSeries.coeff m
            (ons_decFormalFirstReturn L a b d ^ k))
      push_cast
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hsign : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ k = -1 := by
        rw [← pow_add]
        have heven : Even (k + k) := ⟨k, by omega⟩
        rw [show k + 1 + k = (k + k) + 1 by omega,
          pow_succ, heven.neg_one_pow]
        ring
      let c := MvPowerSeries.coeff m
        (ons_decFormalFirstReturn L a b d ^ k)
      change -(c / (k : ℂ)) =
        ((-1 : ℂ) ^ (k + 1) / (k : ℂ)) *
          ((-1 : ℂ) ^ k * c)
      calc
        -(c / (k : ℂ)) = (-1 : ℂ) * c / (k : ℂ) := by ring
        _ = (((-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ k) * c) /
            (k : ℂ) := by rw [hsign]
        _ = ((-1 : ℂ) ^ (k + 1) / (k : ℂ)) *
            ((-1 : ℂ) ^ k * c) := by
              field_simp [hkC]
    · intro n hnk
      have hzero := ons_decFormalFirstReturn_coeff_pow_eq_zero_of_ne_external
        L a b d m n (by simpa only [k] using hnk)
      rw [ons_decFormalFirstReturn_neg_coeff_pow, hzero,
        mul_zero, smul_zero]

theorem ons_decFormalRootedLog_eq_log_subst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalRootedLog L a b d =
      PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
        (PowerSeries.log ℂ) := by
  ext m
  exact ons_decFormalRootedLogCoeff_eq_log_subst L a b d m

theorem ons_powerSeries_deriv_deriv_log :
    PowerSeries.derivative ℂ
        (PowerSeries.derivative ℂ (PowerSeries.log ℂ)) =
      -((PowerSeries.derivative ℂ (PowerSeries.log ℂ)) ^ 2) := by
  open PowerSeries in
    rw [deriv_log]
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, map_neg,
    pow_two, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  have hsum : (∑ p ∈ Finset.antidiagonal n,
      (algebraMap ℚ ℂ) ((-1 : ℚ) ^ p.1) *
        (algebraMap ℚ ℂ) ((-1 : ℚ) ^ p.2)) =
      (n + 1 : ℂ) * ((-1 : ℂ) ^ n) := by
    calc
      _ = ∑ p ∈ Finset.antidiagonal n, ((-1 : ℂ) ^ n) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← map_mul, ← pow_add, Finset.mem_antidiagonal.mp hp]
        simp
      _ = _ := by simp
  rw [hsum]
  push_cast
  rw [pow_succ]
  ring

theorem ons_powerSeries_exp_log :
    PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ) =
      1 + PowerSeries.X := by
  let F := PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ)
  let G := PowerSeries.derivative ℂ (PowerSeries.log ℂ)
  have hchain : PowerSeries.derivative ℂ F = F * G := by
    dsimp only [F, G]
    rw [PowerSeries.derivative_subst ℂ PowerSeries.HasSubst.log,
      PowerSeries.derivative_exp]
  have hG : PowerSeries.derivative ℂ G = -(G ^ 2) :=
    ons_powerSeries_deriv_deriv_log
  have hsecond :
      PowerSeries.derivative ℂ (PowerSeries.derivative ℂ F) = 0 := by
    calc
      PowerSeries.derivative ℂ (PowerSeries.derivative ℂ F) =
          PowerSeries.derivative ℂ (F * G) := by rw [hchain]
      _ = PowerSeries.derivative ℂ F * G +
          F * PowerSeries.derivative ℂ G := by
            simpa [smul_eq_mul, add_comm, mul_comm] using
              Derivation.leibniz (PowerSeries.derivative ℂ) F G
      _ = (F * G) * G + F * (-(G ^ 2)) := by rw [hchain, hG]
      _ = 0 := by ring
  have hcF : PowerSeries.constantCoeff F = 1 := by
    change MvPowerSeries.constantCoeff F = 1
    dsimp only [F]
    rw [PowerSeries.constantCoeff_subst PowerSeries.HasSubst.log]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      have hclog : MvPowerSeries.constantCoeff (PowerSeries.log ℂ) = 0 := by
        exact PowerSeries.constantCoeff_log
      rw [map_pow, hclog, zero_pow hn, smul_zero]
  have hcG : PowerSeries.constantCoeff G = 1 := by
    dsimp only [G]
    rw [PowerSeries.deriv_log]
    simp
  have hcDF :
      PowerSeries.constantCoeff (PowerSeries.derivative ℂ F) = 1 := by
    rw [hchain, map_mul, hcF, hcG, mul_one]
  have hDF : PowerSeries.derivative ℂ F = 1 := by
    apply PowerSeries.derivative.ext
    · rw [hsecond]
      simp
    · rw [hcDF]
      simp
  change F = 1 + PowerSeries.X
  apply PowerSeries.derivative.ext
  · rw [hDF]
    simp
  · rw [hcF]
    simp

theorem ons_decFormalRootedExp_eq_one_sub_firstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.subst (ons_decFormalRootedLog L a b d)
        (PowerSeries.exp ℂ) =
      1 - ons_decFormalFirstReturn L a b d := by
  rw [ons_decFormalRootedLog_eq_log_subst]
  rw [← PowerSeries.subst_comp_subst_apply
    PowerSeries.HasSubst.log
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  rw [ons_powerSeries_exp_log]
  rw [PowerSeries.subst_add
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  have hone : PowerSeries.subst (-ons_decFormalFirstReturn L a b d)
      (1 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom
      (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
    exact map_one _
  rw [hone, PowerSeries.subst_X
    (ons_decFormalFirstReturn_neg_hasSubst L a b d)]
  ring

namespace DecFormalExpAdd

lemma fin2_exp (e : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) (e 0) +
        Finsupp.single (1 : Fin 2) (e 1) = e := by
  ext i
  fin_cases i <;> simp

lemma ex_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2))
        (PowerSeries.exp ℂ)) =
      if e 1 = 0 then (1 : ℂ) / (e 0).factorial else 0 := by
  rw [PowerSeries.coeff_subst_single, PowerSeries.coeff_exp]
  by_cases h : e 1 = 0
  · rw [if_pos h, if_pos]
    · push_cast
      rfl
    · ext i
      fin_cases i <;> simp [h]
  · rw [if_neg h, if_neg]
    intro he
    have he' := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 1) he
    simp at he'
    exact h he'

lemma ey_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2))
        (PowerSeries.exp ℂ)) =
      if e 0 = 0 then (1 : ℂ) / (e 1).factorial else 0 := by
  rw [PowerSeries.coeff_subst_single, PowerSeries.coeff_exp]
  by_cases h : e 0 = 0
  · rw [if_pos h, if_pos]
    · push_cast
      rfl
    · ext i
      fin_cases i <;> simp [h]
  · rw [if_neg h, if_neg]
    intro he
    have he' := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 0) he
    simp at he'
    exact h he'

lemma prod_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2))
          (PowerSeries.exp ℂ) *
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2))
          (PowerSeries.exp ℂ)) =
      (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
  rw [MvPowerSeries.coeff_mul]
  let target : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) :=
    (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))
  rw [Finset.sum_eq_single target]
  · rw [ex_coeff, ey_coeff]
    simp [target]
    ring
  · rintro ⟨p, q⟩ hpq hne
    rw [ex_coeff, ey_coeff]
    by_cases hp : p 1 = 0
    · by_cases hq : q 0 = 0
      · exfalso
        apply hne
        have hadd := Finset.mem_antidiagonal.mp hpq
        dsimp only [target]
        apply Prod.ext
        · ext i
          fin_cases i
          · have hi := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 0) hadd
            simp [hq] at hi ⊢
            exact hi
          · simp [hp]
        · ext i
          fin_cases i
          · simp [hq]
          · have hi := congrArg (fun x : Fin 2 →₀ ℕ ↦ x 1) hadd
            simp [hp] at hi ⊢
            exact hi
      · simp [hq]
    · simp [hp]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_antidiagonal]
    exact fin2_exp e

lemma add_coeff (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2))
        (PowerSeries.exp ℂ)) =
      (1 : ℂ) / ((e 0).factorial * (e 1).factorial) := by
  rw [PowerSeries.coeff_subst
    (PowerSeries.HasSubst.X 0 |>.add (PowerSeries.HasSubst.X 1))]
  rw [finsum_eq_single _ (e 0 + e 1)]
  · rw [PowerSeries.coeff_exp]
    have hcoe :
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) ^
            (e 0 + e 1) =
          (((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^
              (e 0 + e 1) : MvPolynomial (Fin 2) ℂ) :
            MvPowerSeries (Fin 2) ℂ) := by
      simp
    rw [hcoe, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    rw [if_pos]
    · simp only [smul_eq_mul]
      push_cast
      have hfac := Nat.choose_mul_factorial_mul_factorial
        (Nat.le_add_right (e 0) (e 1))
      rw [Nat.add_sub_cancel_left] at hfac
      have heq : ((e 0 + e 1).choose (e 0) : ℂ) *
          ((e 0).factorial : ℂ) * ((e 1).factorial : ℂ) =
          ((e 0 + e 1).factorial : ℂ) := by
        exact_mod_cast hfac
      have h0 : ((e 0).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 0)
      have h1 : ((e 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 1)
      have hs : ((e 0 + e 1).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e 0 + e 1)
      field_simp [h0, h1, hs]
      exact heq
    · rw [Finset.mem_antidiagonal]
  · intro n hn
    have hcoe :
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) ^ n =
          (((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ n :
              MvPolynomial (Fin 2) ℂ) : MvPowerSeries (Fin 2) ℂ) := by
      simp
    rw [hcoe, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    rw [if_neg]
    simp
    rw [Finset.mem_antidiagonal]
    exact fun h ↦ hn h.symm

lemma biv_exp :
    PowerSeries.subst
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) *
      PowerSeries.subst
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) =
      PowerSeries.subst
        ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
          MvPowerSeries (Fin 2) ℂ)
        (PowerSeries.exp ℂ) := by
  ext e
  rw [prod_coeff (e := e), add_coeff (e := e)]

end DecFormalExpAdd

theorem ons_powerSeries_subst_exp_add_of_constantCoeff_zero
    {τ : Type*} (A B : MvPowerSeries τ ℂ)
    (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst A (PowerSeries.exp ℂ) *
      PowerSeries.subst B (PowerSeries.exp ℂ) =
      PowerSeries.subst (A + B) (PowerSeries.exp ℂ) := by
  let v : Fin 2 → MvPowerSeries τ ℂ := ![A, B]
  have hv : MvPowerSeries.HasSubst v :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i ↦ by
      fin_cases i <;> simp [v, hA, hB])
  have h := congrArg (MvPowerSeries.subst v) DecFormalExpAdd.biv_exp
  rw [MvPowerSeries.subst_mul hv] at h
  have hX0 : MvPowerSeries.subst v
      (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ) = A := by
    rw [MvPowerSeries.subst_X hv]
    rfl
  have hX1 : MvPowerSeries.subst v
      (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ) = B := by
    rw [MvPowerSeries.subst_X hv]
    rfl
  have hXadd : MvPowerSeries.subst v
      ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
        MvPowerSeries (Fin 2) ℂ) = A + B := by
    rw [MvPowerSeries.subst_add hv, hX0, hX1]
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    PowerSeries.subst_def] at h
  have hv0 : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using
      (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.X (0 : Fin 2)))
  have hv1 : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using
      (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.X (1 : Fin 2)))
  have hvadd : MvPowerSeries.HasSubst
      (fun _ : Unit ↦
        ((MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) :
          MvPowerSeries (Fin 2) ℂ)) := by
    simpa only using PowerSeries.hasSubst_iff.mp
      ((PowerSeries.HasSubst.X (0 : Fin 2)).add
        (PowerSeries.HasSubst.X (1 : Fin 2)))
  rw [MvPowerSeries.subst_comp_subst_apply hv0 hv,
    MvPowerSeries.subst_comp_subst_apply hv1 hv,
    MvPowerSeries.subst_comp_subst_apply hvadd hv,
    hX0, hX1, hXadd] at h
  exact h

theorem ons_decFormalRootedLog_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalRootedLog L a b d) = 0 := by
  change ons_decFormalRootedLogCoeff L a b d 0 = 0
  apply ons_decFormalRootedLogCoeff_eq_zero_of_external_zero
  rfl

theorem ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_decFormalAvoidRoot L a b d *
        (1 - ons_decFormalFirstReturn L a b d) := by
  unfold ons_decFormalRoot
  rw [ons_decFormalLog_eq_rooted_add_avoid L a b d]
  rw [← ons_powerSeries_subst_exp_add_of_constantCoeff_zero
    (ons_decFormalRootedLog L a b d)
    (ons_decFormalAvoidLog L a b d)
    (ons_decFormalRootedLog_constantCoeff L a b d)
    (ons_decFormalAvoidLog_constantCoeff L a b d)]
  rw [ons_decFormalRootedExp_eq_one_sub_firstReturn]
  unfold ons_decFormalAvoidRoot
  ring

theorem ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : 1 < m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m (1 - ons_decFormalFirstReturn L a b d) = 0 := by
  rw [map_sub]
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hmedge
  rw [MvPowerSeries.coeff_one, if_neg hm0]
  have hm1 : m s(d, ons_dartRev L d) ≠ 1 := by omega
  change 0 - ons_decFormalFirstReturnCoeff L a b d m = 0
  rw [ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one
    L a b d m hm1]
  simp

theorem ons_decFormalRoot_coeff_eq_zero_of_external_ge_two
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : 1 < m s(d, ons_dartRev L d)) :
    MvPowerSeries.coeff m
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  classical
  rw [ons_decFormalRoot_eq_avoidRoot_mul_one_sub_firstReturn L a b d]
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hadd := congrArg (fun x : ons_DecEdge L →₀ ℕ ↦
    x s(d, ons_dartRev L d)) (Finset.mem_antidiagonal.mp hpq)
  simp only [Finsupp.add_apply] at hadd
  by_cases hp : p s(d, ons_dartRev L d) = 0
  · have hq : 1 < q s(d, ons_dartRev L d) := by omega
    rw [ons_one_sub_decFormalFirstReturn_coeff_eq_zero_of_external_ge_two
      L a b d q hq, mul_zero]
  · rw [ons_decFormalAvoidRoot_coeff_eq_zero_of_external
      L a b d p hp, zero_mul]

end StatMech.Onsager
