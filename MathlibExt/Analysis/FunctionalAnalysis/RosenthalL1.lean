/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth

/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

private def rosenthalInitialSegment (φ : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map φ

private def rosenthalAccepts (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ →
    ∃ n : ℕ, 𝒜 (s ++ rosenthalInitialSegment (φ ∘ ψ) n)

private def rosenthalRejects (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ → ¬ rosenthalAccepts 𝒜 s (φ ∘ ψ)

private theorem rosenthal_accepts_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalAccepts 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalAccepts 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

private theorem rosenthal_rejects_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalRejects 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalRejects 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

private theorem rosenthal_not_mem_of_rejects
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalRejects 𝒜 s φ) : ¬𝒜 s := by
  intro hs
  have ha : rosenthalAccepts 𝒜 s φ := by
    intro ψ hψ
    exact ⟨0, by simpa [rosenthalInitialSegment] using hs⟩
  exact h id strictMono_id (by simpa using ha)

private theorem rosenthal_exists_indices_of_range_subset
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hsub : Set.range ψ ⊆ Set.range φ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ψ = φ ∘ θ := by
  have hex : ∀ n, ∃ m, φ m = ψ n := by
    intro n
    obtain ⟨m, hm⟩ := hsub ⟨n, rfl⟩
    exact ⟨m, hm⟩
  choose θ hθ using hex
  have hθmono : StrictMono θ := by
    intro i j hij
    apply (hφ.lt_iff_lt).mp
    rw [hθ i, hθ j]
    exact hψ hij
  exact ⟨θ, hθmono, funext fun n => (hθ n).symm⟩

private theorem rosenthal_decision_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) (hsub : Set.range ψ ⊆ Set.range φ)
    (hdec : rosenthalAccepts 𝒜 s φ ∨ rosenthalRejects 𝒜 s φ) :
    rosenthalAccepts 𝒜 s ψ ∨ rosenthalRejects 𝒜 s ψ := by
  obtain ⟨θ, hθ, rfl⟩ := rosenthal_exists_indices_of_range_subset hφ hψ hsub
  rcases hdec with ha | hr
  · exact Or.inl (rosenthal_accepts_subsequence ha hθ)
  · exact Or.inr (rosenthal_rejects_subsequence hr hθ)

private theorem rosenthal_exists_deciding_subsequence
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (rosenthalAccepts 𝒜 s (φ ∘ ψ) ∨ rosenthalRejects 𝒜 s (φ ∘ ψ)) := by
  classical
  by_cases h : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ rosenthalAccepts 𝒜 s (φ ∘ ψ)
  · obtain ⟨ψ, hψ, ha⟩ := h
    exact ⟨ψ, hψ, Or.inl ha⟩
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    intro ψ hψ ha
    exact h ⟨ψ, hψ, by simpa using ha⟩

private def rosenthalTail (φ : ℕ → ℕ) : ℕ → ℕ :=
  fun n => φ (n + 1)

private theorem rosenthal_initialSegment_succ (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalInitialSegment φ (n + 1) =
      φ 0 :: rosenthalInitialSegment (rosenthalTail φ) n := by
  simp [rosenthalInitialSegment, List.range_succ_eq_map, rosenthalTail,
    Function.comp_def]

private theorem rosenthal_tail_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalTail φ) := by
  exact hφ.comp fun _ _ h => Nat.add_lt_add_right h 1

private noncomputable def rosenthalDecisionIndices
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : ℕ → ℕ :=
  Classical.choose (rosenthal_exists_deciding_subsequence 𝒜 s φ)

private theorem rosenthal_decisionIndices_strictMono
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    StrictMono (rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).1

private theorem rosenthal_decisionIndices_decides
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    rosenthalAccepts 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) ∨
      rosenthalRejects 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).2

private noncomputable def rosenthalDecideMany
    (𝒜 : List ℕ → Prop) : List (List ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | [], φ => φ
  | s :: ss, φ => rosenthalDecideMany 𝒜 ss (φ ∘ rosenthalDecisionIndices 𝒜 s φ)

private theorem rosenthal_decideMany_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => exact hφ
  | cons s ss ih =>
      exact ih (hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 s φ))

private theorem rosenthal_range_decideMany_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalDecideMany 𝒜 ss φ) ⊆ Set.range φ := by
  induction ss generalizing φ with
  | nil => exact Set.Subset.rfl
  | cons s ss ih =>
      exact (ih (φ ∘ rosenthalDecisionIndices 𝒜 s φ)).trans
        (Set.range_comp_subset_range _ _)

private theorem rosenthal_decideMany_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 s (rosenthalDecideMany 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 s (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => simp
  | cons t ts ih =>
      intro s hs
      let φ' := φ ∘ rosenthalDecisionIndices 𝒜 t φ
      have hφ' : StrictMono φ' :=
        hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 t φ)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact rosenthal_decision_subsequence hφ'
          (rosenthal_decideMany_strictMono 𝒜 ts hφ')
          (rosenthal_range_decideMany_subset 𝒜 ts φ')
          (rosenthal_decisionIndices_decides 𝒜 s φ)
      · exact ih hφ' s hs

private noncomputable def rosenthalManyNext
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) : ℕ → ℕ :=
  rosenthalDecideMany 𝒜 (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ)

private theorem rosenthal_manyNext_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyNext 𝒜 ss φ) :=
  rosenthal_decideMany_strictMono 𝒜 _ (rosenthal_tail_strictMono hφ)

private theorem rosenthal_range_manyNext_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyNext 𝒜 ss φ) ⊆ Set.range φ := by
  exact (rosenthal_range_decideMany_subset 𝒜 _ _).trans
    (Set.range_comp_subset_range (fun n => n + 1) φ)

private theorem rosenthal_manyNext_above
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, φ 0 < rosenthalManyNext 𝒜 ss φ n := by
  intro n
  obtain ⟨k, hk⟩ := rosenthal_range_decideMany_subset 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) ⟨n, rfl⟩
  change φ 0 < rosenthalDecideMany 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) n
  rw [← hk]
  exact hφ (Nat.zero_lt_succ k)

private theorem rosenthal_manyNext_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) := by
  intro s hs
  exact rosenthal_decideMany_decides 𝒜 _ (rosenthal_tail_strictMono hφ)
    (s ++ [φ 0]) (List.mem_map.mpr ⟨s, hs, rfl⟩)

private noncomputable def rosenthalManyChain
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  (rosenthalManyNext 𝒜 ss)^[n] φ

private theorem rosenthal_manyChain_succ
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalManyChain 𝒜 ss φ (n + 1) =
      rosenthalManyNext 𝒜 ss (rosenthalManyChain 𝒜 ss φ n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalManyNext 𝒜 ss) n φ

private theorem rosenthal_manyChain_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, StrictMono (rosenthalManyChain 𝒜 ss φ n) := by
  intro n
  induction n with
  | zero => exact hφ
  | succ n ih =>
      rw [rosenthal_manyChain_succ]
      exact rosenthal_manyNext_strictMono 𝒜 ss ih

private theorem rosenthal_range_manyChain_mono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    Set.range (rosenthalManyChain 𝒜 ss φ n) ⊆
      Set.range (rosenthalManyChain 𝒜 ss φ m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
      rw [rosenthal_manyChain_succ]
      exact (rosenthal_range_manyNext_subset 𝒜 ss _).trans ih

private noncomputable def rosenthalManyPoints
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) : ℕ :=
  rosenthalManyChain 𝒜 ss φ n 0

private theorem rosenthal_manyPoints_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyPoints 𝒜 ss φ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [rosenthalManyPoints, rosenthalManyPoints, rosenthal_manyChain_succ]
  exact rosenthal_manyNext_above 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) 0

private theorem rosenthal_range_manyPoints_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyPoints 𝒜 ss φ) ⊆ Set.range φ := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_manyChain_mono 𝒜 ss φ (Nat.zero_le n)
  exact ⟨0, rfl⟩

private theorem rosenthal_manyPoints_tail_subsequence
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧
      rosenthalTail (rosenthalManyPoints 𝒜 ss φ ∘ ψ) =
        rosenthalManyChain 𝒜 ss φ (ψ 0 + 1) ∘ θ := by
  let p := rosenthalManyPoints 𝒜 ss φ
  let q := rosenthalTail (p ∘ ψ)
  have hp : StrictMono p := rosenthal_manyPoints_strictMono 𝒜 ss hφ
  have hq : StrictMono q := rosenthal_tail_strictMono (hp.comp hψ)
  have hsub : Set.range q ⊆
      Set.range (rosenthalManyChain 𝒜 ss φ (ψ 0 + 1)) := by
    rintro _ ⟨j, rfl⟩
    have hle : ψ 0 + 1 ≤ ψ (j + 1) := Nat.succ_le_of_lt (hψ (Nat.zero_lt_succ j))
    apply rosenthal_range_manyChain_mono 𝒜 ss φ hle
    exact ⟨0, rfl⟩
  exact rosenthal_exists_indices_of_range_subset
    (rosenthal_manyChain_strictMono 𝒜 ss hφ (ψ 0 + 1)) hq hsub

private theorem rosenthal_manyPoints_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : List ℕ} (hs : s ∈ ss) (n : ℕ) :
    rosenthalAccepts 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) ∨
      rosenthalRejects 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
  rw [rosenthal_manyChain_succ]
  exact rosenthal_manyNext_decides 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) s hs

private theorem rosenthal_manyPoints_eventually_rejects
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : List ℕ} (hs : s ∈ ss) (hrej : rosenthalRejects 𝒜 s φ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      rosenthalRejects 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
  classical
  by_contra hb
  push Not at hb
  have hunbounded : ∀ N : ℕ, ∃ n > N,
      rosenthalAccepts 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
    intro N
    obtain ⟨n, hn, hnrej⟩ := hb (N + 1)
    refine ⟨n, lt_of_lt_of_le (Nat.lt_succ_self N) hn, ?_⟩
    rcases rosenthal_manyPoints_decides 𝒜 ss hφ hs n with ha | hr
    · exact ha
    · exact False.elim (hnrej hr)
  obtain ⟨η, hη, hηacc⟩ := Nat.exists_strictMono_subsequence hunbounded
  let p := rosenthalManyPoints 𝒜 ss φ
  have hp : StrictMono p := rosenthal_manyPoints_strictMono 𝒜 ss hφ
  let q := p ∘ η
  have hq : StrictMono q := hp.comp hη
  have hqacc : rosenthalAccepts 𝒜 s q := by
    intro ψ hψ
    obtain ⟨θ, hθ, htail⟩ := rosenthal_manyPoints_tail_subsequence 𝒜 ss hφ (hη.comp hψ)
    obtain ⟨k, hk⟩ := hηacc (ψ 0) θ hθ
    refine ⟨k + 1, ?_⟩
    rw [rosenthal_initialSegment_succ]
    have htail' : rosenthalInitialSegment
        (rosenthalManyChain 𝒜 ss φ (η (ψ 0) + 1) ∘ θ) k =
        rosenthalInitialSegment (rosenthalTail (q ∘ ψ)) k := by
      simpa [p, q, Function.comp_def] using
        congrArg (fun q => rosenthalInitialSegment q k) htail.symm
    rw [← htail']
    simpa [p, q, Function.comp_def, List.append_assoc] using hk
  have hqrange : Set.range q ⊆ Set.range φ :=
    (Set.range_comp_subset_range η p).trans
      (rosenthal_range_manyPoints_subset 𝒜 ss φ)
  obtain ⟨θ, hθ, hqcomp⟩ := rosenthal_exists_indices_of_range_subset hφ hq hqrange
  exact hrej θ hθ (by simpa [hqcomp] using hqacc)

private theorem rosenthal_rejected_extensions_step
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hrej : ∀ s ∈ ss, rosenthalRejects 𝒜 s φ) :
    ∃ m : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ j, m < ψ j) ∧
      Set.range ψ ⊆ Set.range φ ∧ m ∈ Set.range φ ∧
      ∀ s ∈ ss, rosenthalRejects 𝒜 (s ++ [m]) ψ := by
  have hcommon : ∀ tt : List (List ℕ), (∀ t ∈ tt, t ∈ ss) →
      ∃ N : ℕ, ∀ t ∈ tt, ∀ n, N ≤ n →
        rosenthalRejects 𝒜 (t ++ [rosenthalManyPoints 𝒜 ss φ n])
          (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
    intro tt htt
    induction tt with
    | nil => exact ⟨0, by simp⟩
    | cons t ts ih =>
        obtain ⟨Nt, hNt⟩ := rosenthal_manyPoints_eventually_rejects
          𝒜 ss hφ (htt t (List.mem_cons_self)) (hrej t (htt t (List.mem_cons_self)))
        obtain ⟨Ns, hNs⟩ := ih (fun u hu => htt u (List.mem_cons_of_mem _ hu))
        refine ⟨max Nt Ns, ?_⟩
        intro u hu n hn
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hNt n ((le_max_left _ _).trans hn)
        · exact hNs u hu n ((le_max_right _ _).trans hn)
  obtain ⟨N, hN⟩ := hcommon ss (fun _ h => h)
  let m := rosenthalManyPoints 𝒜 ss φ N
  let ψ := rosenthalManyChain 𝒜 ss φ (N + 1)
  have hψ : StrictMono ψ := rosenthal_manyChain_strictMono 𝒜 ss hφ (N + 1)
  refine ⟨m, ψ, hψ, ?_, ?_, ?_, ?_⟩
  · intro j
    change rosenthalManyChain 𝒜 ss φ N 0 <
      rosenthalManyChain 𝒜 ss φ (N + 1) j
    rw [rosenthal_manyChain_succ]
    exact rosenthal_manyNext_above 𝒜 ss
      (rosenthal_manyChain_strictMono 𝒜 ss hφ N) j
  · exact rosenthal_range_manyChain_mono 𝒜 ss φ (Nat.zero_le (N + 1))
  · exact rosenthal_range_manyPoints_subset 𝒜 ss φ ⟨N, rfl⟩
  · intro s hs
    exact hN s hs N le_rfl

private structure RosenthalFusionState (𝒜 : List ℕ → Prop) where
  chosen : List ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  rejected : ∀ s ∈ chosen.sublists, rosenthalRejects 𝒜 s tail

private structure RosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) where
  point : ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  above : ∀ n, point < tail n
  tail_subset : Set.range tail ⊆ Set.range st.tail
  point_mem : point ∈ Set.range st.tail
  rejected : ∀ s ∈ (st.chosen ++ [point]).sublists, rosenthalRejects 𝒜 s tail

private theorem rosenthal_fusionStep_exists
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    Nonempty (RosenthalFusionStep 𝒜 st) := by
  obtain ⟨m, ψ, hψ, habove, hsub, hmem, hnew⟩ :=
    rosenthal_rejected_extensions_step 𝒜 st.chosen.sublists st.tail_strict st.rejected
  have hold : ∀ s ∈ st.chosen.sublists, rosenthalRejects 𝒜 s ψ := by
    obtain ⟨θ, hθ, hcomp⟩ :=
      rosenthal_exists_indices_of_range_subset st.tail_strict hψ hsub
    intro s hs
    rw [hcomp]
    exact rosenthal_rejects_subsequence (st.rejected s hs) hθ
  refine ⟨⟨m, ψ, hψ, habove, hsub, hmem, ?_⟩⟩
  intro s hs
  rw [List.sublists_concat] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hold s hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hnew t ht

private noncomputable def rosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionStep 𝒜 st :=
  Classical.choice (rosenthal_fusionStep_exists 𝒜 st)

private noncomputable def rosenthalFusionNext
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionState 𝒜 where
  chosen := st.chosen ++ [(rosenthalFusionStep 𝒜 st).point]
  tail := (rosenthalFusionStep 𝒜 st).tail
  tail_strict := (rosenthalFusionStep 𝒜 st).tail_strict
  rejected := (rosenthalFusionStep 𝒜 st).rejected

private def rosenthalFusionInitial
    (𝒜 : List ℕ → Prop) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hrej : rosenthalRejects 𝒜 [] φ) : RosenthalFusionState 𝒜 where
  chosen := []
  tail := φ
  tail_strict := hφ
  rejected := by
    intro s hs
    simp only [List.sublists_nil, List.mem_singleton] at hs
    simpa [hs] using hrej

private noncomputable def rosenthalFusionStates
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
    RosenthalFusionState 𝒜 :=
  (rosenthalFusionNext 𝒜)^[n] st

private theorem rosenthal_fusionStates_succ
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
    rosenthalFusionStates 𝒜 st (n + 1) =
      rosenthalFusionNext 𝒜 (rosenthalFusionStates 𝒜 st n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalFusionNext 𝒜) n st

private noncomputable def rosenthalFusionPoints
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) : ℕ :=
  (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point

private theorem rosenthal_fusionStates_chosen
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (hst : st.chosen = []) :
    ∀ n, (rosenthalFusionStates 𝒜 st n).chosen =
      rosenthalInitialSegment (rosenthalFusionPoints 𝒜 st) n := by
  intro n
  induction n with
  | zero => exact hst
  | succ n ih =>
      rw [rosenthal_fusionStates_succ]
      change (rosenthalFusionStates 𝒜 st n).chosen ++
          [rosenthalFusionPoints 𝒜 st n] = _
      rw [ih]
      simp [rosenthalInitialSegment, List.range_succ]

private theorem rosenthal_fusionPoints_strictMono
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    StrictMono (rosenthalFusionPoints 𝒜 st) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let cur := rosenthalFusionStates 𝒜 st n
  let step := rosenthalFusionStep 𝒜 cur
  have hstate : rosenthalFusionStates 𝒜 st (n + 1) = rosenthalFusionNext 𝒜 cur :=
    rosenthal_fusionStates_succ 𝒜 st n
  have hmem := (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point_mem
  rw [hstate] at hmem
  obtain ⟨j, hj⟩ := hmem
  change step.point <
    (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point
  rw [hstate, ← hj]
  exact step.above j

private theorem rosenthal_range_fusionState_tail_subset
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    ∀ n, Set.range (rosenthalFusionStates 𝒜 st n).tail ⊆ Set.range st.tail := by
  intro n
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
      rw [rosenthal_fusionStates_succ]
      exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).tail_subset.trans ih

private theorem rosenthal_range_fusionPoints_subset
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    Set.range (rosenthalFusionPoints 𝒜 st) ⊆ Set.range st.tail := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_fusionState_tail_subset 𝒜 st n
  exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point_mem

private theorem rosenthal_initialSegment_comp_sublist
    (φ : ℕ → ℕ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    ∀ n, (rosenthalInitialSegment (φ ∘ ψ) n).Sublist
      (rosenthalInitialSegment φ (ψ n)) := by
  intro n
  induction n with
  | zero => exact List.nil_sublist _
  | succ n ih =>
      have hleft : rosenthalInitialSegment (φ ∘ ψ) (n + 1) =
          rosenthalInitialSegment (φ ∘ ψ) n ++ [φ (ψ n)] := by
        simp [rosenthalInitialSegment, List.range_succ, Function.comp_def]
      rw [hleft]
      have h₁ := ih.append_right [φ (ψ n)]
      have hmiddle : rosenthalInitialSegment φ (ψ n) ++ [φ (ψ n)] =
          rosenthalInitialSegment φ (ψ n + 1) := by
        simp [rosenthalInitialSegment, List.range_succ]
      rw [hmiddle] at h₁
      have hbound : ψ n + 1 ≤ ψ (n + 1) := Nat.succ_le_of_lt (hψ (Nat.lt_succ_self n))
      have h₂ : (rosenthalInitialSegment φ (ψ n + 1)).Sublist
          (rosenthalInitialSegment φ (ψ (n + 1))) := by
        exact (List.range_sublist.mpr hbound).map φ
      exact h₁.trans h₂

private theorem rosenthal_open_ramsey
    (𝒜 : List ℕ → Prop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ((∀ θ : ℕ → ℕ, StrictMono θ → ∀ n, ¬𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) ∨
        ∀ θ : ℕ → ℕ, StrictMono θ →
          ∃ n, 𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) := by
  obtain ⟨η, hη, hdec⟩ := rosenthal_exists_deciding_subsequence 𝒜 [] φ
  let base := φ ∘ η
  have hbase : StrictMono base := hφ.comp hη
  have hrange : Set.range base ⊆ Set.range φ := Set.range_comp_subset_range η φ
  rcases hdec with ha | hr
  · refine ⟨base, hbase, hrange, Or.inr ?_⟩
    intro θ hθ
    obtain ⟨n, hn⟩ := ha θ hθ
    exact ⟨n, by simpa [base] using hn⟩
  · let st := rosenthalFusionInitial 𝒜 base hbase hr
    let ψ := rosenthalFusionPoints 𝒜 st
    have hψ : StrictMono ψ := rosenthal_fusionPoints_strictMono 𝒜 st
    have hψrange : Set.range ψ ⊆ Set.range φ :=
      (rosenthal_range_fusionPoints_subset 𝒜 st).trans hrange
    refine ⟨ψ, hψ, hψrange, Or.inl ?_⟩
    intro θ hθ n
    have hsub := rosenthal_initialSegment_comp_sublist ψ hθ n
    have hchosen : (rosenthalFusionStates 𝒜 st (θ n)).chosen =
        rosenthalInitialSegment ψ (θ n) := by
      exact rosenthal_fusionStates_chosen 𝒜 st rfl (θ n)
    have hmem : rosenthalInitialSegment (ψ ∘ θ) n ∈
        (rosenthalFusionStates 𝒜 st (θ n)).chosen.sublists := by
      rw [hchosen, List.mem_sublists]
      exact hsub
    exact rosenthal_not_mem_of_rejects
      ((rosenthalFusionStates 𝒜 st (θ n)).rejected _ hmem)

private def rosenthalPairsHold {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) : List ℕ → Prop
  | a :: b :: s => R k a b ∧ rosenthalPairsHold R k s
  | _ => True

private theorem rosenthal_pairsHold_initial_even {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) (φ : ℕ → ℕ) :
    ∀ N, rosenthalPairsHold R k (rosenthalInitialSegment φ (2 * N)) ↔
      ∀ j < N, R k (φ (2 * j)) (φ (2 * j + 1)) := by
  intro N
  induction N generalizing φ with
  | zero => simp [rosenthalInitialSegment, rosenthalPairsHold]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        rosenthal_initialSegment_succ, rosenthal_initialSegment_succ]
      simp only [rosenthalPairsHold]
      rw [ih]
      constructor
      · rintro ⟨hzero, htail⟩ j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simpa [rosenthalTail] using hzero
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
          have hi : i < N := by omega
          change R k (φ (2 * (i + 1))) (φ (2 * (i + 1) + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using htail i hi
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [rosenthalTail] using h 0 (Nat.zero_lt_succ N)
        · intro i hi
          change R k (φ (2 * i + 1 + 1)) (φ (2 * i + 1 + 1 + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using h (i + 1) (by omega)

private theorem rosenthal_exists_finite_pair_obstruction
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (R : K → ℕ → ℕ → Prop) (hclosed : ∀ i j, IsClosed {k | R k i j})
    (φ : ℕ → ℕ) (h : ¬∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))) :
    ∃ N, ¬∃ k, ∀ n < N, R k (φ (2 * n)) (φ (2 * n + 1)) := by
  let U : ℕ → Set K := fun n => {k | ¬R k (φ (2 * n)) (φ (2 * n + 1))}
  have hopen : ∀ n, IsOpen (U n) := by
    intro n
    exact (hclosed _ _).isOpen_compl
  have hcover : Set.univ ⊆ ⋃ n, U n := by
    intro k hk
    rw [Set.mem_iUnion]
    by_contra hnone
    push Not at hnone
    have hall : ∀ n, R k (φ (2 * n)) (φ (2 * n + 1)) := by
      intro n
      simpa only [U, Set.mem_ofPred_eq, not_not] using hnone n
    exact h ⟨k, hall⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨t.sup id + 1, ?_⟩
  rintro ⟨k, hk⟩
  have hkt := ht (Set.mem_univ k)
  simp only [Set.mem_iUnion] at hkt
  obtain ⟨n, hnmem, hnU⟩ := hkt
  have hnlt : n < t.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hnmem)
  exact hnU (hk n hnlt)

private def rosenthalPaired {K : Type*}
    (R : K → ℕ → ℕ → Prop) (φ : ℕ → ℕ) : Prop :=
  ∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))

private def rosenthalPairObstruction {K : Type*}
    (R : K → ℕ → ℕ → Prop) (s : List ℕ) : Prop :=
  ∃ N, s.length = 2 * N ∧ ¬∃ k, rosenthalPairsHold R k s

private theorem rosenthal_closed_ramsey
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (R : K → ℕ → ℕ → Prop) (hclosed : ∀ i j, IsClosed {k | R k i j})
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ((∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired R (ψ ∘ θ)) ∨
        ∀ θ : ℕ → ℕ, StrictMono θ → ¬rosenthalPaired R (ψ ∘ θ)) := by
  obtain ⟨ψ, hψ, hψrange, hhom⟩ :=
    rosenthal_open_ramsey (rosenthalPairObstruction R) hφ
  refine ⟨ψ, hψ, hψrange, ?_⟩
  rcases hhom with hnone | hall
  · left
    intro θ hθ
    by_contra hp
    obtain ⟨N, hN⟩ :=
      rosenthal_exists_finite_pair_obstruction R hclosed (ψ ∘ θ) hp
    apply hnone θ hθ (2 * N)
    refine ⟨N, by simp [rosenthalInitialSegment], ?_⟩
    rintro ⟨k, hk⟩
    apply hN
    exact ⟨k, (rosenthal_pairsHold_initial_even R k (ψ ∘ θ) N).mp hk⟩
  · right
    intro θ hθ hp
    obtain ⟨n, hn⟩ := hall θ hθ
    obtain ⟨N, hlen, hno⟩ := hn
    have hne : n = 2 * N := by
      simpa [rosenthalInitialSegment] using hlen
    subst n
    obtain ⟨k, hk⟩ := hp
    apply hno
    refine ⟨k, (rosenthal_pairsHold_initial_even R k (ψ ∘ θ) N).mpr ?_⟩
    intro j hj
    exact hk j

private theorem rosenthal_finite_closed_ramsey
    {C K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (colors : Finset C) (R : C → K → ℕ → ℕ → Prop)
    (hclosed : ∀ c i j, IsClosed {k | R c k i j})
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hcover : ∀ θ : ℕ → ℕ, StrictMono θ →
      ∃ c ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
        rosenthalPaired (R c) (φ ∘ θ ∘ η)) :
    ∃ c ∈ colors, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (R c) (ψ ∘ θ) := by
  classical
  induction colors using Finset.induction_on generalizing φ with
  | empty =>
      obtain ⟨c, hc, η, hη, hp⟩ := hcover id strictMono_id
      simp at hc
  | @insert c colors hc ih =>
      obtain ⟨ψ, hψ, hψrange, hhom⟩ := rosenthal_closed_ramsey (R c) (hclosed c) hφ
      rcases hhom with hpos | hneg
      · exact ⟨c, Finset.mem_insert_self c colors, ψ, hψ, hψrange, hpos⟩
      · obtain ⟨ρ, hρ, hψeq⟩ :=
          rosenthal_exists_indices_of_range_subset hφ hψ hψrange
        have hcoverψ : ∀ θ : ℕ → ℕ, StrictMono θ →
            ∃ d ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
              rosenthalPaired (R d) (ψ ∘ θ ∘ η) := by
          intro θ hθ
          obtain ⟨d, hd, η, hη, hpair⟩ := hcover (ρ ∘ θ) (hρ.comp hθ)
          rw [Finset.mem_insert] at hd
          have hpair' : rosenthalPaired (R d) (ψ ∘ θ ∘ η) := by
            simpa [hψeq, Function.comp_def] using hpair
          rcases hd with rfl | hd
          · exact (hneg (θ ∘ η) (hθ.comp hη)
              (by simpa [Function.comp_def] using hpair')).elim
          · exact ⟨d, hd, η, hη, hpair'⟩
        obtain ⟨d, hd, χ, hχ, hχrange, hall⟩ := ih hψ hcoverψ
        exact ⟨d, Finset.mem_insert_of_mem hd, χ, hχ,
          hχrange.trans hψrange, hall⟩

private def rosenthalPairLift (η : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * η (n / 2) + n % 2

private theorem rosenthal_pairLift_even (η : ℕ → ℕ) (n : ℕ) :
    rosenthalPairLift η (2 * n) = 2 * η n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp only [rosenthalPairLift, hdiv, hmod, add_zero]

private theorem rosenthal_pairLift_odd (η : ℕ → ℕ) (n : ℕ) :
    rosenthalPairLift η (2 * n + 1) = 2 * η n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp only [rosenthalPairLift, hdiv, hmod]

private theorem rosenthal_pairLift_strictMono
    {η : ℕ → ℕ} (hη : StrictMono η) : StrictMono (rosenthalPairLift η) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_pairLift_even, rosenthal_pairLift_odd]
    omega
  · rw [rosenthal_pairLift_odd,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      rosenthal_pairLift_even]
    have h : η k < η (k + 1) := by simpa using hη (Nat.lt_succ_self k)
    omega

private def rosenthalCellPair {K 𝕜 : Type*} [Dist 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜) (k : K) (i j : ℕ) : Prop :=
  dist (f i k) u ≤ delta ∧ dist (f j k) v ≤ delta

private theorem rosenthal_exists_finite_scalar_net
    {𝕜 : Type*} [RCLike 𝕜] (B δ : ℝ) (hδ : 0 < δ) :
    ∃ t : Finset 𝕜, ∀ z : 𝕜, ‖z‖ ≤ B → ∃ u ∈ t, dist z u ≤ δ := by
  have hcover : Metric.closedBall (0 : 𝕜) B ⊆ ⋃ u, Metric.ball u δ := by
    intro z hz
    rw [Set.mem_iUnion]
    exact ⟨z, Metric.mem_ball_self hδ⟩
  obtain ⟨t, ht⟩ := (ProperSpace.isCompact_closedBall (0 : 𝕜) B).elim_finite_subcover
    (fun u => Metric.ball u δ) (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : 𝕜) B := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hzt := ht hzball
  simp only [Set.mem_iUnion] at hzt
  obtain ⟨u, hut, hzu⟩ := hzt
  exact ⟨u, hut, (Metric.mem_ball.mp hzu).le⟩

private def rosenthalGap {K alpha : Type*} [Dist alpha]
    (f : ℕ → K → alpha) (epsilon : ℝ) (k : K) (i j : ℕ) : Prop :=
  epsilon ≤ dist (f i k) (f j k)

private theorem rosenthal_exists_uniform_cell_pair
    {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [RCLike 𝕜] (f : ℕ → K → 𝕜) (hf : ∀ n, Continuous (f n))
    (B epsilon delta : ℝ) (hdelta : 0 < delta)
    (hbound : ∀ n k, ‖f n k‖ ≤ B) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsep : ∀ θ : ℕ → ℕ, StrictMono θ →
      rosenthalPaired (rosenthalGap f epsilon) (φ ∘ θ)) :
    ∃ u v : 𝕜, epsilon ≤ dist u v + 2 * delta ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
        ∀ θ : ℕ → ℕ, StrictMono θ →
          rosenthalPaired (rosenthalCellPair f delta u v) (ψ ∘ θ) := by
  classical
  obtain ⟨t, ht⟩ := rosenthal_exists_finite_scalar_net (𝕜 := 𝕜) B delta hdelta
  let colors := (t.product t).filter fun uv => epsilon ≤ dist uv.1 uv.2 + 2 * delta
  let R : 𝕜 × 𝕜 → K → ℕ → ℕ → Prop := fun uv =>
    rosenthalCellPair f delta uv.1 uv.2
  have hclosed : ∀ c i j, IsClosed {k | R c k i j} := by
    intro c i j
    exact (isClosed_le ((hf i).dist continuous_const) continuous_const).and
      (isClosed_le ((hf j).dist continuous_const) continuous_const)
  have hcover : ∀ θ : ℕ → ℕ, StrictMono θ →
      ∃ c ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
        rosenthalPaired (R c) (φ ∘ θ ∘ η) := by
    intro θ hθ
    obtain ⟨k, hgap⟩ := hsep θ hθ
    have hpick : ∀ n, ∃ c : ↑(t.product t),
        dist (f ((φ ∘ θ) (2 * n)) k) c.1.1 ≤ delta ∧
          dist (f ((φ ∘ θ) (2 * n + 1)) k) c.1.2 ≤ delta := by
      intro n
      obtain ⟨u, hu, hfu⟩ := ht _ (hbound _ _)
      obtain ⟨v, hv, hfv⟩ := ht _ (hbound _ _)
      exact ⟨⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩⟩, hfu, hfv⟩
    choose color hleft hright using hpick
    obtain ⟨c, hcinf⟩ := Finite.exists_infinite_fiber color
    have hinf : (color ⁻¹' ({c} : Set _)).Infinite := Set.infinite_coe_iff.mp hcinf
    let η : ℕ → ℕ := Nat.nth fun n => n ∈ color ⁻¹' ({c} : Set _)
    have hη : StrictMono η := Nat.nth_strictMono hinf
    have hcolor : ∀ n, color (η n) = c := by
      intro n
      simpa [η] using Nat.nth_mem_of_infinite hinf n
    have hvalid : epsilon ≤ dist c.1.1 c.1.2 + 2 * delta := by
      have hc0 := hcolor 0
      have hl := hleft (η 0)
      have hr := hright (η 0)
      rw [hc0] at hl hr
      have htri := dist_triangle4
        (f ((φ ∘ θ) (2 * η 0)) k) c.1.1 c.1.2
        (f ((φ ∘ θ) (2 * η 0 + 1)) k)
      have hg := hgap (η 0)
      rw [rosenthalGap] at hg
      have hr' : dist c.1.2 (f ((φ ∘ θ) (2 * η 0 + 1)) k) ≤ delta := by
        simpa [dist_comm] using hr
      linarith
    refine ⟨c.1, ?_, rosenthalPairLift η, rosenthal_pairLift_strictMono hη, ?_⟩
    · exact Finset.mem_filter.mpr ⟨c.2, hvalid⟩
    · refine ⟨k, ?_⟩
      intro n
      have hc := hcolor n
      have hl := hleft (η n)
      have hr := hright (η n)
      rw [hc] at hl hr
      simpa [R, rosenthalCellPair, Function.comp_def,
        rosenthal_pairLift_even, rosenthal_pairLift_odd] using And.intro hl hr
  obtain ⟨c, hc, ψ, hψ, hψrange, hall⟩ :=
    rosenthal_finite_closed_ramsey colors R hclosed hφ hcover
  exact ⟨c.1, c.2, (Finset.mem_filter.mp hc).2, ψ, hψ, hψrange, hall⟩

private def rosenthalAssignmentIndices (P : Finset ℕ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    if n / 2 ∈ P then 3 * (n / 2) + 1 else 3 * (n / 2)
  else
    if n / 2 ∈ P then 3 * (n / 2) + 2 else 3 * (n / 2) + 1

private theorem rosenthal_assignmentIndices_even (P : Finset ℕ) (n : ℕ) :
    rosenthalAssignmentIndices P (2 * n) =
      if n ∈ P then 3 * n + 1 else 3 * n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

private theorem rosenthal_assignmentIndices_odd (P : Finset ℕ) (n : ℕ) :
    rosenthalAssignmentIndices P (2 * n + 1) =
      if n ∈ P then 3 * n + 2 else 3 * n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

private theorem rosenthal_assignmentIndices_strictMono (P : Finset ℕ) :
    StrictMono (rosenthalAssignmentIndices P) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_assignmentIndices_even, rosenthal_assignmentIndices_odd]
    split <;> omega
  · rw [rosenthal_assignmentIndices_odd,
      show 2 * i + 1 + 1 = 2 * (i + 1) by omega,
      rosenthal_assignmentIndices_even]
    split <;> split <;> omega

private theorem rosenthal_cell_pair_assignments
    {K 𝕜 : Type*} [PseudoMetricSpace 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hall : ∀ θ : ℕ → ℕ, StrictMono θ →
      rosenthalPaired (rosenthalCellPair f delta u v) (φ ∘ θ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ∀ P Q : Finset ℕ, Disjoint P Q → ∃ k : K,
        (∀ i ∈ P, dist (f (ψ i) k) u ≤ delta) ∧
          ∀ i ∈ Q, dist (f (ψ i) k) v ≤ delta := by
  classical
  let sparse : ℕ → ℕ := fun n => 3 * n + 1
  have hsparse : StrictMono sparse := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [sparse]
    omega
  refine ⟨φ ∘ sparse, hφ.comp hsparse, Set.range_comp_subset_range sparse φ, ?_⟩
  intro P Q hPQ
  obtain ⟨k, hk⟩ := hall (rosenthalAssignmentIndices P)
    (rosenthal_assignmentIndices_strictMono P)
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    have hpair := (hk i).1
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_even, hi] using hpair
  · intro i hi
    have hnot : i ∉ P := by
      intro hip
      exact Finset.disjoint_left.mp hPQ hip hi
    have hpair := (hk i).2
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_odd, hnot] using hpair

private theorem rosenthal_norm_le_abs_re_add_abs_im
    {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  rw [← RCLike.re_add_im z]
  refine (norm_add_le _ _).trans ?_
  rw [RCLike.norm_ofReal, norm_mul, RCLike.norm_ofReal, RCLike.norm_I]
  split <;> simp [abs_nonneg]

private theorem rosenthal_exists_large_quadrant
    {𝕜 : Type*} [RCLike 𝕜] (s : Finset ℕ) (z : ℕ → 𝕜) :
    ∃ P : Finset ℕ, P ⊆ s ∧
      (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ P, z i‖ := by
  classical
  let rp := s.filter fun i => 0 ≤ RCLike.re (z i)
  let rn := s.filter fun i => ¬0 ≤ RCLike.re (z i)
  let ip := s.filter fun i => 0 ≤ RCLike.im (z i)
  let inn := s.filter fun i => ¬0 ≤ RCLike.im (z i)
  have hrp : (∑ i ∈ rp, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rp, z i‖ := by
    calc
      (∑ i ∈ rp, |RCLike.re (z i)|) = ∑ i ∈ rp, RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.re (∑ i ∈ rp, z i) := by
        symm
        exact map_sum RCLike.re _ _
      _ ≤ ‖∑ i ∈ rp, z i‖ := RCLike.re_le_norm _
  have hrn : (∑ i ∈ rn, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rn, z i‖ := by
    calc
      (∑ i ∈ rn, |RCLike.re (z i)|) = ∑ i ∈ rn, -RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.re (∑ i ∈ rn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.re : 𝕜 →+ ℝ) z rn).symm
      _ ≤ ‖∑ i ∈ rn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.re_le_norm (-(∑ i ∈ rn, z i))
  have hip : (∑ i ∈ ip, |RCLike.im (z i)|) ≤ ‖∑ i ∈ ip, z i‖ := by
    calc
      (∑ i ∈ ip, |RCLike.im (z i)|) = ∑ i ∈ ip, RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.im (∑ i ∈ ip, z i) := by
        symm
        exact map_sum RCLike.im _ _
      _ ≤ ‖∑ i ∈ ip, z i‖ := RCLike.im_le_norm _
  have hinn : (∑ i ∈ inn, |RCLike.im (z i)|) ≤ ‖∑ i ∈ inn, z i‖ := by
    calc
      (∑ i ∈ inn, |RCLike.im (z i)|) = ∑ i ∈ inn, -RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.im (∑ i ∈ inn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.im : 𝕜 →+ ℝ) z inn).symm
      _ ≤ ‖∑ i ∈ inn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.im_le_norm (-(∑ i ∈ inn, z i))
  have hre : (∑ i ∈ s, |RCLike.re (z i)|) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.re (z i)) (fun i => |RCLike.re (z i)|)]
    change (∑ i ∈ rp, |RCLike.re (z i)|) + (∑ i ∈ rn, |RCLike.re (z i)|) ≤ _
    exact add_le_add hrp hrn
  have him : (∑ i ∈ s, |RCLike.im (z i)|) ≤
      ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.im (z i)) (fun i => |RCLike.im (z i)|)]
    change (∑ i ∈ ip, |RCLike.im (z i)|) + (∑ i ∈ inn, |RCLike.im (z i)|) ≤ _
    exact add_le_add hip hinn
  have htotal : (∑ i ∈ s, ‖z i‖) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ +
        ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    have hcoord : (∑ i ∈ s, ‖z i‖) ≤
        (∑ i ∈ s, |RCLike.re (z i)|) +
          ∑ i ∈ s, |RCLike.im (z i)| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => rosenthal_norm_le_abs_re_add_abs_im (z i)
    linarith
  by_cases h : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rp, z i‖
  · exact ⟨rp, Finset.filter_subset _ _, h⟩
  by_cases h' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rn, z i‖
  · exact ⟨rn, Finset.filter_subset _ _, h'⟩
  by_cases h'' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ ip, z i‖
  · exact ⟨ip, Finset.filter_subset _ _, h''⟩
  refine ⟨inn, Finset.filter_subset _ _, ?_⟩
  by_contra h'''
  push Not at h h' h'' h'''
  linarith

private abbrev RosenthalDualBall (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  {g : WeakDual 𝕜 E //
    WeakDual.toStrongDual g ∈ Metric.closedBall (0 : StrongDual 𝕜 E) 1}

private noncomputable instance rosenthalDualBallCompact
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CompactSpace (RosenthalDualBall 𝕜 E) :=
  isCompact_iff_compactSpace.mp
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1)

private instance rosenthalDualBallNonempty
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Nonempty (RosenthalDualBall 𝕜 E) :=
  ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩

private noncomputable def rosenthalDualBallStrong
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : RosenthalDualBall 𝕜 E) : StrongDual 𝕜 E :=
  WeakDual.toStrongDual g.1

private theorem rosenthal_dualBallStrong_norm_le
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : RosenthalDualBall 𝕜 E) : ‖rosenthalDualBallStrong g‖ ≤ 1 := by
  simpa [rosenthalDualBallStrong, Metric.mem_closedBall, dist_eq_norm] using g.2

private noncomputable def rosenthalDualEval
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) : 𝕜 :=
  g.1 (x n)

private theorem rosenthal_dualEval_continuous
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) : Continuous (rosenthalDualEval (𝕜 := 𝕜) x n) :=
  (WeakDual.eval_continuous (x n)).comp continuous_subtype_val

private theorem rosenthal_dualEval_eq_strong
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) :
    rosenthalDualEval (𝕜 := 𝕜) x n g =
      rosenthalDualBallStrong (𝕜 := 𝕜) g (x n) := by
  exact (WeakDual.toStrongDual_apply g.1 (x n)).symm

private theorem rosenthal_dual_sum_error
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (y : ℕ → E) (u v : 𝕜) (delta : ℝ)
    (a : ℕ →₀ 𝕜) (P : Finset ℕ) (hP : P ⊆ a.support)
    (g h : RosenthalDualBall 𝕜 E)
    (hgu : ∀ i ∈ a.support \ P,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ delta)
    (hgv : ∀ i ∈ P,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ delta)
    (hhu : ∀ i ∈ a.support,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i h) u ≤ delta) :
    ‖rosenthalDualBallStrong g (∑ i ∈ a.support, a i • y i) -
        rosenthalDualBallStrong h (∑ i ∈ a.support, a i • y i) -
          ∑ i ∈ P, a i * (v - u)‖ ≤
      2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
  classical
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let target : ℕ → 𝕜 := fun i => if i ∈ P then v - u else 0
  have herr : ∀ i ∈ a.support,
      ‖(F (y i) - G (y i)) - target i‖ ≤ 2 * delta := by
    intro i hi
    by_cases hiP : i ∈ P
    · have hFv : ‖F (y i) - v‖ ≤ delta := by
        simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgv i hiP
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = v - u by simp [target, hiP]]
      rw [show (F (y i) - G (y i)) - (v - u) =
          (F (y i) - v) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
    · have hiDiff : i ∈ a.support \ P := Finset.mem_sdiff.mpr ⟨hi, hiP⟩
      have hFu : ‖F (y i) - u‖ ≤ delta := by
        simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgu i hiDiff
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = 0 by simp [target, hiP], sub_zero]
      rw [show F (y i) - G (y i) = (F (y i) - u) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
  have hsum : ‖∑ i ∈ a.support,
      a i * ((F (y i) - G (y i)) - target i)‖ ≤
      2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
    calc
      ‖∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i)‖ ≤
          ∑ i ∈ a.support, ‖a i * ((F (y i) - G (y i)) - target i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ a.support, ‖a i‖ * (2 * delta) := by
        exact Finset.sum_le_sum fun i hi => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (herr i hi) (norm_nonneg _)
      _ = 2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have htarget : (∑ i ∈ a.support, a i * target i) =
      ∑ i ∈ P, a i * (v - u) := by
    calc
      (∑ i ∈ a.support, a i * target i) = ∑ i ∈ P, a i * target i := by
        symm
        exact Finset.sum_subset hP fun i hi hiP => by simp [target, hiP]
      _ = ∑ i ∈ P, a i * (v - u) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [target, hi]
  have heq :
      F (∑ i ∈ a.support, a i • y i) -
          G (∑ i ∈ a.support, a i • y i) -
            ∑ i ∈ P, a i * (v - u) =
        ∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i) := by
    rw [map_sum, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← htarget, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change ‖F (∑ i ∈ a.support, a i • y i) -
      G (∑ i ∈ a.support, a i • y i) -
        ∑ i ∈ P, a i * (v - u)‖ ≤ _
  rw [heq]
  exact hsum

/-- **Uniform $\ell^1$ lower bound.** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. A sequence $(y_i)_{i \in \mathbb{N}}$ in $E$ has a uniform $\ell^1$ lower bound when
there is a real $c > 0$ such that $\|\sum_i a_i y_i\| \ge c \sum_i |a_i|$ for every finitely
supported sequence $(a_i)_{i \in \mathbb{N}}$ of scalars in $\mathbb{K}$, both sums running over
the finitely many $i$ with $a_i \ne 0$. -/
def HasUniformL1LowerBound {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (y : ℕ → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ →₀ 𝕜),
    ‖∑ i ∈ a.support, a i • y i‖ ≥ c * ∑ i ∈ a.support, ‖a i‖

private theorem rosenthal_uniform_lower_bound_of_assignments
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (y : ℕ → E) (epsilon : ℝ) (hepsilon : 0 < epsilon) (u v : 𝕜)
    (hcenters : epsilon ≤ dist u v + 2 * (epsilon / 64))
    (hassign : ∀ P Q : Finset ℕ, Disjoint P Q →
      ∃ g : RosenthalDualBall 𝕜 E,
        (∀ i ∈ P,
          dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ epsilon / 64) ∧
        ∀ i ∈ Q,
          dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ epsilon / 64) :
    HasUniformL1LowerBound (𝕜 := 𝕜) y := by
  refine ⟨epsilon / 16, by positivity, ?_⟩
  intro a
  let total : ℝ := ∑ i ∈ a.support, ‖a i‖
  let S : E := ∑ i ∈ a.support, a i • y i
  obtain ⟨P, hP, hquadrant⟩ := rosenthal_exists_large_quadrant a.support
    (fun i => a i * (v - u))
  obtain ⟨g, hgu, hgv⟩ := hassign (a.support \ P) P Finset.sdiff_disjoint
  obtain ⟨h, hhu, _⟩ := hassign a.support ∅ (by simp)
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let Z : 𝕜 := ∑ i ∈ P, a i * (v - u)
  have herror : ‖F S - G S - Z‖ ≤ 2 * (epsilon / 64) * total := by
    simpa [F, G, S, Z, total] using
      rosenthal_dual_sum_error y u v (epsilon / 64) a P hP g h hgu hgv hhu
  have hF : ‖F S‖ ≤ ‖S‖ := by
    calc
      ‖F S‖ ≤ ‖F‖ * ‖S‖ := ContinuousLinearMap.le_opNorm F S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hG : ‖G S‖ ≤ ‖S‖ := by
    calc
      ‖G S‖ ≤ ‖G‖ * ‖S‖ := ContinuousLinearMap.le_opNorm G S
      _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right
        (rosenthal_dualBallStrong_norm_le h) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hdiff : ‖F S - G S‖ ≤ 2 * ‖S‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have htriangle : ‖Z‖ ≤ ‖F S - G S - Z‖ + ‖F S - G S‖ := by
    calc
      ‖Z‖ = ‖(Z - (F S - G S)) + (F S - G S)‖ := by congr 1; ring
      _ ≤ ‖Z - (F S - G S)‖ + ‖F S - G S‖ := norm_add_le _ _
      _ = ‖F S - G S - Z‖ + ‖F S - G S‖ := by rw [norm_sub_rev]
  have hZupper : ‖Z‖ ≤ 2 * (epsilon / 64) * total + 2 * ‖S‖ :=
    htriangle.trans (add_le_add herror hdiff)
  have hnormsum : (∑ i ∈ a.support, ‖a i * (v - u)‖) = dist u v * total := by
    simp only [norm_mul]
    rw [← Finset.sum_mul]
    simp [total, dist_eq_norm, norm_sub_rev, mul_comm]
  have hZlower : dist u v * total / 4 ≤ ‖Z‖ := by
    rw [hnormsum] at hquadrant
    simpa [Z] using hquadrant
  have htotal : 0 ≤ total := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcenter' : epsilon - 2 * (epsilon / 64) ≤ dist u v := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hcenter' htotal
  change epsilon / 16 * total ≤ ‖S‖
  nlinarith

private theorem rosenthal_dualEval_bounded
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ B : ℝ, ∀ n (g : RosenthalDualBall 𝕜 E),
      ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ ≤ B := by
  obtain ⟨B, hB⟩ := hx.subset_closedBall 0
  refine ⟨B, ?_⟩
  intro n g
  have hxn : ‖x n‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hB ⟨n, rfl⟩
  calc
    ‖rosenthalDualEval (𝕜 := 𝕜) x n g‖ =
        ‖rosenthalDualBallStrong g (x n)‖ := by
      rw [rosenthal_dualEval_eq_strong]
    _ ≤ ‖rosenthalDualBallStrong g‖ * ‖x n‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x n‖ := mul_le_mul_of_nonneg_right
      (rosenthal_dualBallStrong_norm_le g) (norm_nonneg _)
    _ ≤ B := by simpa using hxn

private theorem rosenthal_weakCauchy_of_dualBall
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (φ : ℕ → ℕ)
    (h : ∀ g : RosenthalDualBall 𝕜 E, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        dist (rosenthalDualEval (𝕜 := 𝕜) x (φ m) g)
          (rosenthalDualEval (𝕜 := 𝕜) x (φ n) g) < epsilon) :
    ∀ (f : E →L[𝕜] 𝕜) (epsilon : ℝ), 0 < epsilon →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        ‖f (x (φ m)) - f (x (φ n))‖ < epsilon := by
  intro f epsilon hepsilon
  by_cases hf : f = 0
  · subst f
    exact ⟨0, fun _ _ _ _ => by simpa using hepsilon⟩
  · have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let c : 𝕜 := ((‖f‖⁻¹ : ℝ) : 𝕜)
    let f' : E →L[𝕜] 𝕜 := c • f
    have hcnorm : ‖c‖ = ‖f‖⁻¹ := by
      simp [c]
    have hf'norm : ‖f'‖ ≤ 1 := by
      change ‖c • f‖ ≤ 1
      rw [norm_smul, hcnorm, inv_mul_cancel₀ (ne_of_gt hfnorm)]
    let g : RosenthalDualBall 𝕜 E :=
      ⟨StrongDual.toWeakDual f', by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hf'norm⟩
    have hepsdiv : 0 < epsilon / ‖f‖ := div_pos hepsilon hfnorm
    obtain ⟨N, hN⟩ := h g (epsilon / ‖f‖) hepsdiv
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hclose := hN m n hm hn
    change dist ((StrongDual.toWeakDual f') (x (φ m)))
      ((StrongDual.toWeakDual f') (x (φ n))) < epsilon / ‖f‖ at hclose
    rw [StrongDual.toWeakDual_apply, StrongDual.toWeakDual_apply] at hclose
    have hscaled : ‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖ < epsilon / ‖f‖ := by
      change dist (c * f (x (φ m))) (c * f (x (φ n))) < epsilon / ‖f‖ at hclose
      rw [dist_eq_norm, ← mul_sub, norm_mul, hcnorm] at hclose
      exact hclose
    have hmul := mul_lt_mul_of_pos_left hscaled hfnorm
    calc
      ‖f (x (φ m)) - f (x (φ n))‖ =
          ‖f‖ * (‖f‖⁻¹ * ‖f (x (φ m)) - f (x (φ n))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hfnorm), one_mul]
      _ < ‖f‖ * (epsilon / ‖f‖) := hmul
      _ = epsilon := by
        rw [div_eq_mul_inv]
        calc
          ‖f‖ * (epsilon * ‖f‖⁻¹) = epsilon * (‖f‖ * ‖f‖⁻¹) := by ring
          _ = epsilon := by rw [mul_inv_cancel₀ (ne_of_gt hfnorm), mul_one]

private theorem rosenthal_exists_paired_subsequence_of_not_eventually_close
    {α : Type*} [PseudoMetricSpace α] (u : ℕ → α) {ε : ℝ} (hε : 0 < ε)
    (h : ¬∃ N, ∀ m n, N ≤ m → N ≤ n → dist (u m) (u n) < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, ε ≤ dist (u (φ (2 * j))) (u (φ (2 * j + 1))) := by
  push Not at h
  have hpick : ∀ N : ℕ, ∃ a b : ℕ,
      N ≤ a ∧ a < b ∧ ε ≤ dist (u a) (u b) := by
    intro N
    obtain ⟨m, n, hm, hn, hmn⟩ := h N
    have hne : m ≠ n := by
      intro heq
      subst n
      simpa using (lt_of_lt_of_le hε hmn).ne'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨m, n, hm, hlt, hmn⟩
    · exact ⟨n, m, hn, hgt, by simpa [dist_comm] using hmn⟩
  choose lo hi hlo hlthi hgap using hpick
  let next : ℕ → ℕ := fun N => hi N + 1
  let bound : ℕ → ℕ := fun n => next^[n] 0
  let left : ℕ → ℕ := fun n => lo (bound n)
  let right : ℕ → ℕ := fun n => hi (bound n)
  let φ : ℕ → ℕ := fun n =>
    if n % 2 = 0 then left (n / 2) else right (n / 2)
  have hbound_succ : ∀ n, bound (n + 1) = right n + 1 := by
    intro n
    rw [show n + 1 = n.succ from rfl]
    exact Function.iterate_succ_apply' next n 0
  have hφeven : ∀ n, φ (2 * n) = left n := by
    intro n
    have hdiv : 2 * n / 2 = n := by omega
    have hmod : 2 * n % 2 = 0 := by omega
    simp only [φ, hdiv, hmod, ↓reduceIte]
  have hφodd : ∀ n, φ (2 * n + 1) = right n := by
    intro n
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    simp only [φ, hdiv, hmod, one_ne_zero, ↓reduceIte]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [hφeven, hφodd]
      exact hlthi _
    · rw [hφodd, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hφeven]
      have hnext : right k + 1 ≤ left (k + 1) := by
        rw [← hbound_succ]
        exact hlo _
      omega
  exact ⟨φ, hφ, fun j => by rw [hφeven, hφodd]; exact hgap _⟩

private theorem rosenthal_eventually_close_of_no_gap_paired
    {K α : Type*} [PseudoMetricSpace α] (f : ℕ → K → α) {ε : ℝ} (hε : 0 < ε)
    {φ : ℕ → ℕ}
    (hno : ∀ θ : ℕ → ℕ, StrictMono θ →
      ¬rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)) :
    ∀ k : K, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      dist (f (φ m) k) (f (φ n) k) < ε := by
  intro k
  by_contra hclose
  obtain ⟨θ, hθ, hgap⟩ :=
    rosenthal_exists_paired_subsequence_of_not_eventually_close
      (fun n => f (φ n) k) hε hclose
  apply hno θ hθ
  exact ⟨k, fun j => by simpa [rosenthalGap, Function.comp_def] using hgap j⟩

private structure RosenthalSequenceState where
  seq : ℕ → ℕ
  strict : StrictMono seq

private theorem rosenthal_pointwiseCauchy_or_uniformlySeparated
    {K α : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [PseudoMetricSpace α] (f : ℕ → K → α) (hf : ∀ n, Continuous (f n)) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : K, ∀ ε : ℝ, 0 < ε →
        ∃ N, ∀ m n, N ≤ m → N ≤ n → dist (f (φ m) k) (f (φ n) k) < ε := by
  classical
  by_cases hsep : ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)
  · exact Or.inl hsep
  · have heps : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      intro n
      positivity
    have hstep : ∀ (n : ℕ) (st : RosenthalSequenceState),
        ∃ next : RosenthalSequenceState,
          Set.range next.seq ⊆ Set.range st.seq ∧
          (∀ j, st.seq 0 < next.seq j) ∧
          ∀ θ : ℕ → ℕ, StrictMono θ →
            ¬rosenthalPaired (rosenthalGap f (1 / ((n : ℝ) + 1))) (next.seq ∘ θ) := by
      intro n st
      let δ : ℝ := 1 / ((n : ℝ) + 1)
      let tail := rosenthalTail st.seq
      have htail : StrictMono tail := rosenthal_tail_strictMono st.strict
      have hclosed : ∀ i j, IsClosed {k | rosenthalGap f δ k i j} := by
        intro i j
        exact isClosed_le continuous_const ((hf i).dist (hf j))
      obtain ⟨ψ, hψ, hψrange, hhom⟩ := rosenthal_closed_ramsey
        (rosenthalGap f δ) hclosed htail
      have hrange : Set.range ψ ⊆ Set.range st.seq :=
        hψrange.trans (Set.range_comp_subset_range (fun q => q + 1) st.seq)
      have habove : ∀ j, st.seq 0 < ψ j := by
        intro j
        obtain ⟨q, hq⟩ := hψrange ⟨j, rfl⟩
        rw [← hq]
        exact st.strict (Nat.zero_lt_succ q)
      rcases hhom with hpos | hneg
      · exfalso
        apply hsep
        exact ⟨δ, heps n, ψ, hψ, hpos⟩
      · exact ⟨⟨ψ, hψ⟩, hrange, habove, hneg⟩
    choose step hstep_range hstep_above hstep_nogap using hstep
    let states : ℕ → RosenthalSequenceState := fun n =>
      Nat.rec ⟨id, strictMono_id⟩ (fun n st => step n st) n
    have hstates_zero : states 0 = ⟨id, strictMono_id⟩ := rfl
    have hstates_succ : ∀ n, states (n + 1) = step n (states n) := fun n => rfl
    let φ : ℕ → ℕ := fun n => (states n).seq 0
    have hφ : StrictMono φ := by
      apply strictMono_nat_of_lt_succ
      intro n
      change (states n).seq 0 < (states (n + 1)).seq 0
      rw [hstates_succ]
      exact hstep_above n (states n) 0
    have hstates_range : ∀ {m n : ℕ}, m ≤ n →
        Set.range (states n).seq ⊆ Set.range (states m).seq := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact Set.Subset.rfl
      | succ n hmn ih =>
          rw [hstates_succ]
          exact (hstep_range n (states n)).trans ih
    refine Or.inr ⟨φ, hφ, ?_⟩
    intro k ε hε
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
    have hno := hstep_nogap q (states q)
    rw [← hstates_succ q] at hno
    have hbase := rosenthal_eventually_close_of_no_gap_paired
      f (heps q) hno k
    let tailφ : ℕ → ℕ := fun j => φ (q + 1 + j)
    have htailφ : StrictMono tailφ :=
      hφ.comp fun _ _ h => Nat.add_lt_add_left h (q + 1)
    have htailrange : Set.range tailφ ⊆ Set.range (states (q + 1)).seq := by
      rintro _ ⟨j, rfl⟩
      apply hstates_range (Nat.le_add_right (q + 1) j)
      exact ⟨0, rfl⟩
    obtain ⟨η, hη, htailcomp⟩ := rosenthal_exists_indices_of_range_subset
      (states (q + 1)).strict htailφ htailrange
    obtain ⟨N, hN⟩ := hbase
    refine ⟨q + 1 + N, ?_⟩
    intro m n hm hn
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
    have hηm : N ≤ η (N + m') :=
      (Nat.le_add_right N m').trans (StrictMono.id_le hη (N + m'))
    have hηn : N ≤ η (N + n') :=
      (Nat.le_add_right N n').trans (StrictMono.id_le hη (N + n'))
    have hclose := hN (η (N + m')) (η (N + n')) hηm hηn
    have hm_eq : tailφ (N + m') = (states (q + 1)).seq (η (N + m')) := by
      simpa only [Function.comp_apply] using congrFun htailcomp (N + m')
    have hn_eq : tailφ (N + n') = (states (q + 1)).seq (η (N + n')) := by
      simpa only [Function.comp_apply] using congrFun htailcomp (N + n')
    rw [← hm_eq, ← hn_eq] at hclose
    simpa [tailφ, Nat.add_assoc] using lt_trans hclose hq

/--
**Rosenthal's $\ell^1$ theorem.** Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$ and let $(x_n)_{n \in \mathbb{N}}$ be a bounded sequence in $E$. Then there is a
strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$ such that either the subsequence
$(x_{\varphi(n)})_{n \in \mathbb{N}}$ is weakly Cauchy, that is, for every continuous linear
functional $f : E \to \mathbb{K}$ and every real $\varepsilon > 0$ there is $N$ with
$|f(x_{\varphi(m)}) - f(x_{\varphi(n)})| < \varepsilon$ for all $m, n \ge N$, or
$(x_{\varphi(n)})_{n \in \mathbb{N}}$ has a uniform $\ell^1$ lower bound.

Proves `Wanted` entry `rosenthal_l1`.

Proof: We use the Nash-Williams/Galvin-Prikry Ramsey route, following Rosenthal's 1974 theorem,
Albiac and Kalton, Sections 10.1–10.2, and Farahat's 1974 proof.

Source: H. P. Rosenthal,
A Characterization of Banach Spaces Containing l1, PNAS 71 (1974), 2411–2413,
DOI 10.1073/pnas.71.6.2411, ℓ¹ dichotomy theorem; Bourgain et al., extensions; Lean states
`RCLike` Banach bounded `Set.range` dichotomy with `StrictMono φ` and `HasUniformL1LowerBound`
defined via `ℕ →₀ 𝕜` finitely supported coefficients.
-/
public theorem rosenthal_l1
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ),
      (∀ (f : E →L[𝕜] 𝕜) (ε : ℝ), 0 < ε →
        ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖f (x (φ m)) - f (x (φ n))‖ < ε) ∨
      HasUniformL1LowerBound (𝕜 := 𝕜) (x ∘ φ) := by
  let eval : ℕ → RosenthalDualBall 𝕜 E → 𝕜 :=
    rosenthalDualEval (𝕜 := 𝕜) x
  have heval : ∀ n, Continuous (eval n) :=
    rosenthal_dualEval_continuous (𝕜 := 𝕜) x
  obtain ⟨B, hB⟩ := rosenthal_dualEval_bounded (𝕜 := 𝕜) x hx
  rcases rosenthal_pointwiseCauchy_or_uniformlySeparated eval heval with hsep | hcauchy
  · obtain ⟨epsilon, hepsilon, φ, hφ, hseparated⟩ := hsep
    obtain ⟨u, v, hcenters, ψ, hψ, hψrange, hcells⟩ :=
      rosenthal_exists_uniform_cell_pair eval heval B epsilon (epsilon / 64)
        (by positivity) hB hφ hseparated
    obtain ⟨χ, hχ, hχrange, hassign⟩ :=
      rosenthal_cell_pair_assignments eval (epsilon / 64) u v hψ hcells
    refine ⟨χ, hχ, Or.inr ?_⟩
    apply rosenthal_uniform_lower_bound_of_assignments (x ∘ χ)
      epsilon hepsilon u v hcenters
    intro P Q hPQ
    obtain ⟨g, hgu, hgv⟩ := hassign P Q hPQ
    exact ⟨g, by
      simpa [eval, rosenthalDualEval, Function.comp_def] using hgu, by
      simpa [eval, rosenthalDualEval, Function.comp_def] using hgv⟩
  · obtain ⟨φ, hφ, hcauchy⟩ := hcauchy
    refine ⟨φ, hφ, Or.inl ?_⟩
    apply rosenthal_weakCauchy_of_dualBall x φ
    simpa [eval] using hcauchy

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
