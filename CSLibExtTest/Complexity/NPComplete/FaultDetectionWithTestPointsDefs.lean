/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FaultDetectionWithTestPointsDefs

namespace MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- The diamond `0 → 1 → 3`, `0 → 2 → 3` with source `0`, sink `3`, and bound `K`. -/
private abbrev diamond (K : ℕ) : FaultDetectionWithTestPointsInstance :=
  (4, [(0, 1), (0, 2), (1, 3), (2, 3)], 0, 3, K)

private theorem adj_iff (K : ℕ) (a b : Fin 4) :
    (Graph (diamond K)).Adj a b ↔ ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (0, 2), (1, 3), (2, 3)] :=
  Iff.rfl

/-- Reachability in the diamond, as an explicit relation. -/
private def Reach (a b : Fin 4) : Prop :=
  a = b ∨ ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]

private instance (a b : Fin 4) : Decidable (Reach a b) := by unfold Reach; infer_instance

/-- Strict reachability in the diamond, as an explicit relation. -/
private def StrictReach (a b : Fin 4) : Prop :=
  ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]

private instance (a b : Fin 4) : Decidable (StrictReach a b) := by
  unfold StrictReach; infer_instance

private theorem reach_trans : ∀ a b c : Fin 4, Reach a b → Reach b c → Reach a c := by
  decide

private theorem strictReach_trans :
    ∀ a b c : Fin 4, StrictReach a b → StrictReach b c → StrictReach a c := by
  decide

private theorem arc_reach : ∀ a b : Fin 4,
    ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (0, 2), (1, 3), (2, 3)] → Reach a b := by
  decide

private theorem arc_strictReach : ∀ a b : Fin 4,
    ((a : ℕ), (b : ℕ)) ∈ [(0, 1), (0, 2), (1, 3), (2, 3)] → StrictReach a b := by
  decide

private theorem reach_iff (K : ℕ) (a b : Fin 4) :
    Relation.ReflTransGen (Graph (diamond K)).Adj a b ↔ Reach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hbc ih => exact reach_trans _ _ _ ih (arc_reach _ _ ((adj_iff K _ _).1 hbc))
  · intro h
    have e : ∀ x y : Fin 4, ((x : ℕ), (y : ℕ)) ∈ [(0, 1), (0, 2), (1, 3), (2, 3)] →
        Relation.ReflTransGen (Graph (diamond K)).Adj x y :=
      fun x y hxy => .single ((adj_iff K x y).2 hxy)
    rcases h with rfl | h
    · exact .refl
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : a = 0 := Fin.ext ha
      obtain rfl : b = 1 := Fin.ext hb
      exact e 0 1 (by decide)
    · obtain rfl : a = 0 := Fin.ext ha
      obtain rfl : b = 2 := Fin.ext hb
      exact e 0 2 (by decide)
    · obtain rfl : a = 0 := Fin.ext ha
      obtain rfl : b = 3 := Fin.ext hb
      exact (e 0 1 (by decide)).trans (e 1 3 (by decide))
    · obtain rfl : a = 1 := Fin.ext ha
      obtain rfl : b = 3 := Fin.ext hb
      exact e 1 3 (by decide)
    · obtain rfl : a = 2 := Fin.ext ha
      obtain rfl : b = 3 := Fin.ext hb
      exact e 2 3 (by decide)

private theorem transGen_strict (K : ℕ) (a b : Fin 4)
    (h : Relation.TransGen (Graph (diamond K)).Adj a b) : StrictReach a b := by
  induction h with
  | single hab => exact arc_strictReach _ _ ((adj_iff K _ _).1 hab)
  | tail _ hbc ih => exact strictReach_trans _ _ _ ih (arc_strictReach _ _ ((adj_iff K _ _).1 hbc))

private theorem onPath_iff (K : ℕ) (u v w : Fin 4) :
    OnPath (diamond K) u v w ↔ Reach u v ∧ Reach v w := by
  unfold OnPath
  rw [reach_iff, reach_iff]

private theorem strictReach_irrefl : ∀ v : Fin 4, ¬ StrictReach v v := by decide

private theorem unique_source :
    ∀ v : Fin 4, (∀ u : Fin 4, ((u : ℕ), (v : ℕ)) ∉ [(0, 1), (0, 2), (1, 3), (2, 3)]) ↔ v = 0 := by
  decide

private theorem unique_sink :
    ∀ v : Fin 4, (∀ w : Fin 4, ((v : ℕ), (w : ℕ)) ∉ [(0, 1), (0, 2), (1, 3), (2, 3)]) ↔ v = 3 := by
  decide

private theorem diamond_wellFormed (K : ℕ) (hK : 0 < K) : WellFormed (diamond K) :=
  ⟨by dsimp only [diamond]; decide, by dsimp only [diamond]; decide,
    fun v h => strictReach_irrefl v (transGen_strict K v v h),
    ⟨0, rfl, fun v => by simp only [adj_iff]; exact unique_source v⟩,
    ⟨3, rfl, fun v => by simp only [adj_iff]; exact unique_sink v⟩, hK⟩

set_option synthInstance.maxSize 1024 in
/-- Test points from no arcs: only `(0, 3)`, on whose paths both inner vertices lie. -/
private theorem no_arc :
    ¬ ∀ v v' : Fin 4, (v : ℕ) ≠ 0 → (v : ℕ) ≠ 3 → (v' : ℕ) ≠ 0 → (v' : ℕ) ≠ 3 → v ≠ v' →
      ∃ u₁ u₂ : Fin 4, (u₁ : ℕ) = 0 ∧ (u₂ : ℕ) = 3 ∧
        (Reach u₁ v ∧ Reach v u₂) ∧ ¬ (Reach u₁ v' ∧ Reach v' u₂) := by
  decide

set_option synthInstance.maxSize 1024 in
/-- Test points from one arc `a` never tell both inner vertices apart. -/
private theorem no_single_arc : ∀ a : Fin 4 × Fin 4,
    ((a.1 : ℕ), (a.2 : ℕ)) ∈ [(0, 1), (0, 2), (1, 3), (2, 3)] →
    ¬ ∀ v v' : Fin 4, (v : ℕ) ≠ 0 → (v : ℕ) ≠ 3 → (v' : ℕ) ≠ 0 → (v' : ℕ) ≠ 3 → v ≠ v' →
      ∃ u₁ u₂ : Fin 4, ((u₁ : ℕ) = 0 ∨ ∃ w, (u₁, w) = a) ∧ ((u₂ : ℕ) = 3 ∨ ∃ w, (w, u₂) = a) ∧
        (Reach u₁ v ∧ Reach v u₂) ∧ ¬ (Reach u₁ v' ∧ Reach v' u₂) := by
  decide

set_option synthInstance.maxSize 1024 in
/-- With bound `2`, the arcs `0 → 1` and `0 → 2` add test points `(0, 1)` and `(0, 2)`, which
tell the two inner vertices apart. -/
example : faultDetectionWithTestPointsDec (bitEncode (diamond 2)) = true := by
  have hf : FaultDetectionWithTestPointsFeasible (diamond 2) := by
    refine ⟨{(0, 1), (0, 2)}, ?_, by decide, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> exact (adj_iff 2 _ _).2 (by decide)
    · simp only [onPath_iff]
      decide
  simp [faultDetectionWithTestPointsDec, bitDecode_bitEncode, diamond_wellFormed 2 (by decide), hf]

/-- With bound `1`, no single arc yields test points telling both inner vertices apart, so the
decision problem rejects the well-formed diamond. -/
example : WellFormed (diamond 1) ∧
    faultDetectionWithTestPointsDec (bitEncode (diamond 1)) = false := by
  have hf : ¬ FaultDetectionWithTestPointsFeasible (diamond 1) := by
    rintro ⟨A, hA, hcard, h⟩
    simp only [onPath_iff] at h
    rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp only [Finset.notMem_empty, exists_false, or_false] at h
      exact no_arc h
    · have hAa : A = {a} := Finset.eq_singleton_iff_unique_mem.2
        ⟨ha, fun b hb => Finset.card_le_one.1 hcard b hb a ha⟩
      subst hAa
      have harc := (adj_iff 1 _ _).1 (hA a (Finset.mem_singleton_self a))
      simp only [Finset.mem_singleton] at h
      exact no_single_arc a harc h
  exact ⟨diamond_wellFormed 1 (by decide),
    by simp [faultDetectionWithTestPointsDec, bitDecode_bitEncode, hf]⟩

/-- A zero bound is malformed, although a path with a single inner vertex needs no test
points. -/
example :
    FaultDetectionWithTestPointsFeasible
        ((3, [(0, 1), (1, 2)], 0, 2, 0) : FaultDetectionWithTestPointsInstance) ∧
      faultDetectionWithTestPointsDec
        (bitEncode ((3, [(0, 1), (1, 2)], 0, 2, 0) : FaultDetectionWithTestPointsInstance)) =
          false := by
  have hw : ¬ WellFormed ((3, [(0, 1), (1, 2)], 0, 2, 0) : FaultDetectionWithTestPointsInstance) :=
    fun h => absurd h.2.2.2.2.2 (by decide)
  refine ⟨⟨∅, by simp, by simp, fun v v' h1 h2 h3 h4 h5 =>
    absurd (Fin.ext (by have := v.2; have := v'.2; dsimp only at h1 h2 h3 h4 this; omega)) h5⟩,
    by simp [faultDetectionWithTestPointsDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : faultDetectionWithTestPointsDec [true] = false := by
  have h : bitDecode (α := FaultDetectionWithTestPointsInstance) [true] = none := rfl
  simp [faultDetectionWithTestPointsDec, h]

end MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints
