/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Sharpness.Claim1IsingComplete
import Code.Sharpness.SwitchingDichotomy
import Code.Ising.TwoReplica

open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech
namespace Sharpness

open FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




theorem summable_gatedSourcePairSummand (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] :
    Summable (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)) := by
  have hprod : Summable (fun pq :
      (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      ‖(if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)‖ *
        ‖(if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0)‖) :=
    Summable.mul_of_nonneg
      (summable_norm_currentSum_summand G β J A)
      (summable_norm_currentSum_summand G β J B)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_norm
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro pq
  by_cases hA : sources G (ofEdgeFun G pq.1) = A <;>
    by_cases hB : sources G (ofEdgeFun G pq.2) = B <;>
    by_cases hP : P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) <;>
    simp [hA, hB, hP, norm_mul] <;> positivity



theorem gatedSourcePairSum_partition (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P]
    (f : Current V → Finset V) :
    gatedSourcePairSum G β J A B P =
      ∑ S : Finset V, gatedSourcePairSum G β J A B (fun m => f m = S ∧ P m) := by
  unfold gatedSourcePairSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (Finset V)))
    (f := fun S (pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ)) =>
      (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if f (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) = S ∧
            P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0))
    (fun S _ => summable_gatedSourcePairSummand G β J A B
      (fun m => f m = S ∧ P m))]
  apply tsum_congr
  intro pq
  let m := ofEdgeFun G (fun e => pq.1 e + pq.2 e)
  by_cases hA : sources G (ofEdgeFun G pq.1) = A <;>
    by_cases hB : sources G (ofEdgeFun G pq.2) = B <;>
    by_cases hP : P m <;> simp [m, hA, hB, hP]


theorem gatedSourcePairSum_congr_sources (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P Q : Current V → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ p q : ↥G.edgeFinset → ℕ,
      sources G (ofEdgeFun G p) = A → sources G (ofEdgeFun G q) = B →
        (P (ofEdgeFun G (fun e => p e + q e)) ↔
          Q (ofEdgeFun G (fun e => p e + q e)))) :
    gatedSourcePairSum G β J A B P = gatedSourcePairSum G β J A B Q := by
  unfold gatedSourcePairSum
  apply tsum_congr
  rintro ⟨p, q⟩
  change
    ((if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0) *
        (if P (ofEdgeFun G (fun e => p e + q e)) then 1 else 0)) =
      ((if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0) *
        (if Q (ofEdgeFun G (fun e => p e + q e)) then 1 else 0))
  by_cases hp : sources G (ofEdgeFun G p) = A <;>
    by_cases hq : sources G (ofEdgeFun G q) = B
  · rw [if_pos hp, if_pos hq]
    by_cases hP : P (ofEdgeFun G (fun e => p e + q e))
    · rw [if_pos hP, if_pos ((h p q hp hq).mp hP)]
    · rw [if_neg hP, if_neg (fun hQ => hP ((h p q hp hq).mpr hQ))]
  · simp [hp, hq]
  · simp [hp]
  · simp [hp]




theorem currentConnected_of_sources_pair (m : ↥G.edgeFinset → ℕ) {u v : V}
    (huv : u ≠ v) (hsrc : sources G (ofEdgeFun G m) = {u, v}) :
    CurrentConnected G (ofEdgeFun G m) u v := by
  have hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeFinset he
  have hodd := Ising.connOdd_of_sources G.edgeFinset (ofEdgeFun G m) hnd huv (by
    simpa only using hsrc)
  have hpos := Ising.connOdd_imp_connPos G.edgeFinset (ofEdgeFun G m) hodd
  change Relation.ReflTransGen
    (Ising.adjP (Ising.posEdges G.edgeFinset (ofEdgeFun G m))) u v at hpos
  unfold CurrentConnected
  refine Relation.ReflTransGen.rec
    (motive := fun z _ => (currentSubgraph G (ofEdgeFun G m)).Reachable u z)
    (SimpleGraph.Reachable.refl u) ?_ hpos
  intro a b hab hstep ih
  apply SimpleGraph.Reachable.trans ih
  apply Adj.reachable
  obtain ⟨e, he, ha, hb, hne⟩ := hstep
  rw [Ising.posEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
  subst heq
  exact ⟨he.1, he.2⟩



theorem current_disconnect_dichotomy (m : ↥G.edgeFinset → ℕ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources G (ofEdgeFun G m) = {o, x, y, g})
    (hng : ¬ CurrentConnected G (ofEdgeFun G m) o g) :
    (CurrentConnected G (ofEdgeFun G m) o x ∧
        CurrentConnected G (ofEdgeFun G m) y g) ∨
      (CurrentConnected G (ofEdgeFun G m) o y ∧
        CurrentConnected G (ofEdgeFun G m) x g) := by
  let U : Finset (FluxEdgeCopy.Copy G m) := Finset.univ
  have hsrcU : RandomCurrent.sources (FluxEdgeCopy.endsM G m) U = {o, x, y, g} := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
    exact hsrc
  have hngU : ¬ RandomCurrent.connK (FluxEdgeCopy.endsM G m) U o g := by
    simpa only [U, FluxEdgeCopy.connK_univ_iff] using hng
  have hd := RandomCurrent.disconnect_dichotomy (FluxEdgeCopy.endsM G m) U
    (fun i _ => FluxEdgeCopy.endsM_not_isDiag G m i)
    hox hoy hog hxy hxg hyg hsrcU hngU
  simpa only [U, FluxEdgeCopy.connK_univ_iff] using hd



theorem deltaSource_comm {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    (({o, g} : Finset V) ∆ {x, y}) = ({y, g} : Finset V) ∆ {o, x} := by
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hzo : z = o <;> by_cases hzx : z = x <;>
    by_cases hzy : z = y <;> by_cases hzg : z = g <;> simp_all [eq_comm]



theorem deltaSource_eq_four {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    (({o, g} : Finset V) ∆ {x, y}) = {o, x, y, g} := by
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · tauto
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]




theorem deltaEvent_notConnComp_iff
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = ({o, g} : Finset V) ∆ {x, y})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o x ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x, y, g} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    rw [deltaSource_eq_four hox hoy hog hxy hxg hyg]
    ext z
    simp [Finset.mem_symmDiff]
  constructor
  · rintro ⟨hS, hoxc, hygC, hnog⟩
    have hoS : o ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m o)
    have hxS : x ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hoxc
    have hgS : g ∈ S := by
      rw [← hS, mem_notConnComp]
      exact hnog
    have hyS : y ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hoyc
      exact hnog (CurrentConnected.trans G hoyc hygC)
    exact ⟨⟨hyS, hgS, hoS, hxS⟩, hS⟩
  · rintro ⟨⟨hyS, hgS, hoS, hxS⟩, hS⟩
    have hny : ¬ CurrentConnected G m o y := by
      rw [← mem_notConnComp, hS]
      exact hyS
    have hng : ¬ CurrentConnected G m o g := by
      rw [← mem_notConnComp, hS]
      exact hgS
    rcases current_disconnect_dichotomy G (fun e => p e + q e)
      hox hoy hog hxy hxg hyg hsrc hng with hcase | hcase
    · exact ⟨hS, hcase.1, hcase.2, hng⟩
    · exact absurd hcase.1 hny



theorem middleEvent_notConnComp_iff {o x y g : V} (hox : o ≠ x)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = {o, x})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext z
    simp [Finset.mem_symmDiff]
  have hoxC : CurrentConnected G m o x :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hox hsrc
  constructor
  · rintro ⟨hS, hygC, hnog⟩
    have hgS : g ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m g)
    have hyS : y ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hygC.symm
    have hoS : o ∈ S := by
      rw [← hS, mem_notConnComp]
      exact fun hgo => hnog hgo.symm
    have hxS : x ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hgx
      exact hnog (CurrentConnected.trans G hoxC hgx.symm)
    exact ⟨⟨hoS, hxS, hyS, hgS⟩, hS⟩
  · rintro ⟨⟨hoS, hxS, hyS, hgS⟩, hS⟩
    have hygC : CurrentConnected G m y g := by
      have : ¬ y ∈ notConnComp G m g := by rw [hS]; exact hyS
      rw [mem_notConnComp] at this
      exact (not_not.mp this).symm
    have hnog : ¬ CurrentConnected G m o g := by
      have : o ∈ notConnComp G m g := by rw [hS]; exact hoS
      rw [mem_notConnComp] at this
      exact fun hogC => this hogC.symm
    exact ⟨hS, hygC, hnog⟩


theorem middleEvent_notConnCompO_iff {o x y g : V} (hox : o ≠ x)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = {o, x})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext z
    simp [Finset.mem_symmDiff]
  have hoxC : CurrentConnected G m o x :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hox hsrc
  constructor
  · rintro ⟨hS, hygC, hnog⟩
    have hoS : o ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m o)
    have hxS : x ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hoxC
    have hgS : g ∈ S := by
      rw [← hS, mem_notConnComp]
      exact hnog
    have hyS : y ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hoyC
      exact hnog (CurrentConnected.trans G hoyC hygC)
    exact ⟨⟨hyS, hgS, hoS, hxS⟩, hS, hygC⟩
  · rintro ⟨⟨hyS, hgS, hoS, hxS⟩, hS, hygC⟩
    have hnog : ¬ CurrentConnected G m o g := by
      rw [← mem_notConnComp, hS]
      exact hgS
    exact ⟨hS, hygC, hnog⟩





noncomputable def isingDeltaPairSum (β : ℝ) (J : Sym2 V → ℝ)
    (o x y g : V) : ℝ :=
  gatedSourcePairSum G β J (({o, g} : Finset V) ∆ {x, y}) ∅
    (fun m => CurrentConnected G m o x ∧ CurrentConnected G m y g ∧
      ¬ CurrentConnected G m o g)



noncomputable def isingDeltaLowerMass (β : ℝ) (J : Sym2 V → ℝ)
    (o x y g : V) : ℝ :=
  ∑ S : Finset V,
    if o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S then
      expectationJ G β (couplingIn J S) {o, x} *
        gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S)
    else 0




noncomputable def isingDeltaSelfLowerMass (β : ℝ) (J : Sym2 V → ℝ)
    (o y g : V) : ℝ :=
  ∑ S : Finset V,
    if o ∈ S ∧ y ∉ S ∧ g ∉ S then
      gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S)
    else 0



theorem sourcePairDisconn_eq_deltaPair_add (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    sourcePairDisconnSum G β J {o, x, y, g} ∅ o g =
      isingDeltaPairSum G β J o x y g +
        isingDeltaPairSum G β J o y x g := by
  let P₁ : Current V → Prop := fun m =>
    CurrentConnected G m o x ∧ CurrentConnected G m y g ∧
      ¬ CurrentConnected G m o g
  let P₂ : Current V → Prop := fun m =>
    CurrentConnected G m o y ∧ CurrentConnected G m x g ∧
      ¬ CurrentConnected G m o g
  have hs₁ := summable_gatedSourcePairSummand G β J {o, x, y, g} ∅ P₁
  have hs₂ := summable_gatedSourcePairSummand G β J {o, x, y, g} ∅ P₂
  unfold sourcePairDisconnSum isingDeltaPairSum gatedSourcePairSum
  rw [deltaSource_eq_four hox hoy hog hxy hxg hyg]
  rw [deltaSource_eq_four hoy hox hog hxy.symm hyg hxg]
  rw [show ({o, y, x, g} : Finset V) = {o, x, y, g} by
    ext z; simp [or_comm, or_left_comm]]
  rw [← hs₁.tsum_add hs₂]
  apply tsum_congr
  rintro ⟨p, q⟩
  let m := ofEdgeFun G (fun e => p e + q e)
  by_cases hp : sources G (ofEdgeFun G p) = {o, x, y, g}
  · by_cases hq : sources G (ofEdgeFun G q) = ∅
    · have hsrc : sources G m = {o, x, y, g} := by
        dsimp [m]
        rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
        ext z
        simp [Finset.mem_symmDiff]
      have hiff : (¬ CurrentConnected G m o g) ↔ P₁ m ∨ P₂ m := by
        constructor
        · intro hng
          rcases current_disconnect_dichotomy G (fun e => p e + q e)
              hox hoy hog hxy hxg hyg hsrc hng with h1 | h2
          · exact Or.inl ⟨h1.1, h1.2, hng⟩
          · exact Or.inr ⟨h2.1, h2.2, hng⟩
        · rintro (h1 | h2)
          · exact h1.2.2
          · exact h2.2.2
      have hdisj : ¬ (P₁ m ∧ P₂ m) := by
        rintro ⟨h1, h2⟩
        exact h1.2.2 (CurrentConnected.trans G h2.1 h1.2.1)
      by_cases hd : CurrentConnected G m o g <;>
        by_cases h1 : P₁ m <;> by_cases h2 : P₂ m <;>
        simp [hp, hq, m, P₁, P₂, hd, h1, h2] at hiff hdisj ⊢
    · simp [hp, hq]
  · simp [hp]



theorem isingDeltaPairSum_nonneg (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (o x y g : V) :
    0 ≤ isingDeltaPairSum G β J o x y g := by
  unfold isingDeltaPairSum gatedSourcePairSum
  apply tsum_nonneg
  rintro ⟨p, q⟩
  by_cases hp : sources G (ofEdgeFun G p) = ({o, g} : Finset V) ∆ {x, y} <;>
    by_cases hq : sources G (ofEdgeFun G q) = ∅ <;>
    by_cases hP : CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o x ∧
      CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
      ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g <;>
    simp [hp, hq, hP]
  exact mul_nonneg
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G p))
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G q))





theorem isingDeltaPairSum_partition_o (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    isingDeltaPairSum G β J o x y g =
      ∑ S : Finset V,
        if y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S then
          gatedSourcePairSum G β J (({o, g} : Finset V) ∆ {x, y}) ∅
            (fun m => notConnComp G m o = S)
        else 0 := by
  unfold isingDeltaPairSum
  rw [gatedSourcePairSum_partition G β J (({o, g} : Finset V) ∆ {x, y}) ∅
    (fun m => CurrentConnected G m o x ∧ CurrentConnected G m y g ∧
      ¬ CurrentConnected G m o g) (fun m => notConnComp G m o)]
  apply Finset.sum_congr rfl
  intro S _
  have hc := gatedSourcePairSum_congr_sources G β J
    (({o, g} : Finset V) ∆ {x, y}) ∅
    (fun m => notConnComp G m o = S ∧
      (CurrentConnected G m o x ∧ CurrentConnected G m y g ∧
        ¬ CurrentConnected G m o g))
    (fun m => (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
      notConnComp G m o = S)
    (fun p q hp hq => deltaEvent_notConnComp_iff G
      hox hoy hog hxy hxg hyg S p q hp hq)
  rw [hc]
  by_cases hgood : y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S
  · rw [if_pos hgood]
    apply gatedSourcePairSum_congr_sources G β J
    intro p q hp hq
    simp [hgood]
  · rw [if_neg hgood]
    unfold gatedSourcePairSum
    simp [hgood]



theorem middlePairSum_partition_o (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V} (hox : o ≠ x) :
    gatedSourcePairSum G β J {o, x} ∅
        (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
      ∑ S : Finset V,
        if y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S then
          gatedSourcePairSum G β J {o, x} ∅
            (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g)
        else 0 := by
  rw [gatedSourcePairSum_partition G β J {o, x} ∅
    (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g)
    (fun m => notConnComp G m o)]
  apply Finset.sum_congr rfl
  intro S _
  have hc := gatedSourcePairSum_congr_sources G β J {o, x} ∅
    (fun m => notConnComp G m o = S ∧
      (CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g))
    (fun m => (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
      notConnComp G m o = S ∧ CurrentConnected G m y g)
    (fun p q hp hq => middleEvent_notConnCompO_iff G hox S p q hp hq)
  rw [hc]
  by_cases hgood : y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S
  · rw [if_pos hgood]
    apply gatedSourcePairSum_congr_sources G β J
    intro p q hp hq
    simp [hgood]
  · rw [if_neg hgood]
    unfold gatedSourcePairSum
    simp [hgood]


theorem middlePairSum_partition_g (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V} (hox : o ≠ x) :
    gatedSourcePairSum G β J {o, x} ∅
        (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
      ∑ S : Finset V,
        if o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S then
          gatedSourcePairSum G β J {o, x} ∅
            (fun m => notConnComp G m g = S)
        else 0 := by
  rw [gatedSourcePairSum_partition G β J {o, x} ∅
    (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g)
    (fun m => notConnComp G m g)]
  apply Finset.sum_congr rfl
  intro S _
  have hc := gatedSourcePairSum_congr_sources G β J {o, x} ∅
    (fun m => notConnComp G m g = S ∧
      (CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g))
    (fun m => (o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S) ∧
      notConnComp G m g = S)
    (fun p q hp hq => middleEvent_notConnComp_iff G hox S p q hp hq)
  rw [hc]
  by_cases hgood : o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S
  · rw [if_pos hgood]
    apply gatedSourcePairSum_congr_sources G β J
    intro p q hp hq
    simp [hgood]
  · rw [if_neg hgood]
    unfold gatedSourcePairSum
    simp [hgood]



theorem claim2_ising_gated (β : ℝ) (J : Sym2 V → ℝ)
    (S : Finset V) (g o x : V) (hg : g ∉ S) (ho : o ∈ S) (hx : x ∈ S) :
    gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m g = S) =
      expectationJ G β (couplingIn J S) {o, x} *
        gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S) := by
  unfold gatedSourcePairSum
  simpa only [ofEdgeFun_add] using claim2_ising G β J S g hg o x ho hx
    (ne_of_gt (Ising.acr_currentSum_empty_pos G β (couplingIn J S)))





theorem sourcePairDisconn_partition_o_self (β : ℝ) (J : Sym2 V → ℝ)
    {o y g : V} (hyg : y ≠ g) :
    sourcePairDisconnSum G β J {y, g} ∅ o g =
      ∑ S : Finset V,
        if y ∈ S ∧ g ∈ S ∧ o ∉ S then
          gatedSourcePairSum G β J {y, g} ∅
            (fun m => notConnComp G m o = S)
        else 0 := by
  have htoGated : sourcePairDisconnSum G β J {y, g} ∅ o g =
      gatedSourcePairSum G β J {y, g} ∅
        (fun m => ¬ CurrentConnected G m o g) := by
    unfold sourcePairDisconnSum gatedSourcePairSum
    apply tsum_congr
    rintro ⟨p, q⟩
    rfl
  rw [htoGated, gatedSourcePairSum_partition G β J {y, g} ∅
    (fun m => ¬ CurrentConnected G m o g) (fun m => notConnComp G m o)]
  apply Finset.sum_congr rfl
  intro S _
  have hc := gatedSourcePairSum_congr_sources G β J {y, g} ∅
    (fun m => notConnComp G m o = S ∧ ¬ CurrentConnected G m o g)
    (fun m => (y ∈ S ∧ g ∈ S ∧ o ∉ S) ∧ notConnComp G m o = S)
    (fun p q hp hq => by
      let m := ofEdgeFun G (fun e => p e + q e)
      have hsrc : sources G m = {y, g} := by
        dsimp [m]
        rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
        ext z
        simp [Finset.mem_symmDiff]
      have hygC : CurrentConnected G m y g :=
        currentConnected_of_sources_pair G (fun e => p e + q e) hyg hsrc
      constructor
      · rintro ⟨hS, hnog⟩
        have hoS : o ∉ S := by
          rw [← hS, mem_notConnComp]
          exact not_not.mpr (CurrentConnected.refl G m o)
        have hgS : g ∈ S := by
          rw [← hS, mem_notConnComp]
          exact hnog
        have hyS : y ∈ S := by
          rw [← hS, mem_notConnComp]
          exact fun hoyC => hnog (CurrentConnected.trans G hoyC hygC)
        exact ⟨⟨hyS, hgS, hoS⟩, hS⟩
      · rintro ⟨⟨_, hgS, _⟩, hS⟩
        refine ⟨hS, ?_⟩
        rw [← mem_notConnComp, hS]
        exact hgS)
  rw [hc]
  by_cases hgood : y ∈ S ∧ g ∈ S ∧ o ∉ S
  · rw [if_pos hgood]
    apply gatedSourcePairSum_congr_sources G β J
    intro p q hp hq
    simp [hgood]
  · rw [if_neg hgood]
    unfold gatedSourcePairSum
    simp [hgood]



theorem middlePairSum_partition_g_self (β : ℝ) (J : Sym2 V → ℝ)
    (o y g : V) :
    gatedSourcePairSum G β J ∅ ∅
        (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
      isingDeltaSelfLowerMass G β J o y g := by
  rw [gatedSourcePairSum_partition G β J ∅ ∅
    (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g)
    (fun m => notConnComp G m g)]
  unfold isingDeltaSelfLowerMass
  apply Finset.sum_congr rfl
  intro S _
  have hc := gatedSourcePairSum_congr_sources G β J ∅ ∅
    (fun m => notConnComp G m g = S ∧
      (CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g))
    (fun m => (o ∈ S ∧ y ∉ S ∧ g ∉ S) ∧ notConnComp G m g = S)
    (fun p q _ _ => by
      let m := ofEdgeFun G (fun e => p e + q e)
      constructor
      · rintro ⟨hS, hygC, hnog⟩
        have hgS : g ∉ S := by
          rw [← hS, mem_notConnComp]
          exact not_not.mpr (CurrentConnected.refl G m g)
        have hyS : y ∉ S := by
          rw [← hS, mem_notConnComp]
          exact not_not.mpr hygC.symm
        have hoS : o ∈ S := by
          rw [← hS, mem_notConnComp]
          exact fun hgo => hnog hgo.symm
        exact ⟨⟨hoS, hyS, hgS⟩, hS⟩
      · rintro ⟨⟨hoS, hyS, _⟩, hS⟩
        have hygC : CurrentConnected G m y g := by
          have hnot : ¬ y ∈ notConnComp G m g := by rw [hS]; exact hyS
          rw [mem_notConnComp] at hnot
          exact (not_not.mp hnot).symm
        have hnog : ¬ CurrentConnected G m o g := by
          have hmem : o ∈ notConnComp G m g := by rw [hS]; exact hoS
          rw [mem_notConnComp] at hmem
          exact fun hogC => hmem hogC.symm
        exact ⟨hS, hygC, hnog⟩)
  rw [hc]
  by_cases hgood : o ∈ S ∧ y ∉ S ∧ g ∉ S
  · rw [if_pos hgood]
    apply gatedSourcePairSum_congr_sources G β J
    intro p q hp hq
    simp [hgood]
  · rw [if_neg hgood]
    unfold gatedSourcePairSum
    simp [hgood]






theorem ising_delta_bound_cleared_self (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {o y g : V} (hyg : y ≠ g) :
    expectationJ G β J {y, g} *
        sourcePairDisconnSum G β J {y, g} ∅ o g ≥
      isingDeltaSelfLowerMass G β J o y g := by
  let goodO : Finset V → Prop := fun S => y ∈ S ∧ g ∈ S ∧ o ∉ S
  let left : Finset V → ℝ := fun S =>
    gatedSourcePairSum G β J {y, g} ∅ (fun m => notConnComp G m o = S)
  let target : Finset V → ℝ := fun S =>
    gatedSourcePairSum G β J ∅ ∅
      (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g)
  have hclaimSum :
      (∑ S : Finset V, if goodO S then target S else 0) ≤
        expectationJ G β J {y, g} *
          ∑ S : Finset V, if goodO S then left S else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    by_cases hgood : goodO S
    · rw [if_pos hgood, if_pos hgood]
      rcases hgood with ⟨hyS, hgS, hoS⟩
      exact claim1_ising_self_cleared G β J hβ hJ S o y g hoS hyS hgS hyg
    · simp [hgood]
  have hdelta : sourcePairDisconnSum G β J {y, g} ∅ o g =
      ∑ S : Finset V, if goodO S then left S else 0 := by
    simpa only [goodO, left] using sourcePairDisconn_partition_o_self G β J hyg
  have hmiddle : gatedSourcePairSum G β J ∅ ∅
      (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
      ∑ S : Finset V, if goodO S then target S else 0 := by
    rw [gatedSourcePairSum_partition G β J ∅ ∅
      (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g)
      (fun m => notConnComp G m o)]
    apply Finset.sum_congr rfl
    intro S _
    have hc := gatedSourcePairSum_congr_sources G β J ∅ ∅
      (fun m => notConnComp G m o = S ∧
        (CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g))
      (fun m => goodO S ∧ notConnComp G m o = S ∧ CurrentConnected G m y g)
      (fun p q _ _ => by
        let m := ofEdgeFun G (fun e => p e + q e)
        constructor
        · rintro ⟨hS, hygC, hnog⟩
          have hoS : o ∉ S := by
            rw [← hS, mem_notConnComp]
            exact not_not.mpr (CurrentConnected.refl G m o)
          have hgS : g ∈ S := by rw [← hS, mem_notConnComp]; exact hnog
          have hyS : y ∈ S := by
            rw [← hS, mem_notConnComp]
            exact fun hoyC => hnog (CurrentConnected.trans G hoyC hygC)
          exact ⟨⟨hyS, hgS, hoS⟩, hS, hygC⟩
        · rintro ⟨⟨_, hgS, _⟩, hS, hygC⟩
          refine ⟨hS, hygC, ?_⟩
          rw [← mem_notConnComp, hS]
          exact hgS)
    rw [hc]
    by_cases hgood : goodO S
    · rw [if_pos hgood]
      apply gatedSourcePairSum_congr_sources G β J
      intro p q hp hq
      simp [hgood, target]
    · rw [if_neg hgood]
      unfold gatedSourcePairSum
      simp [hgood]
  calc
    expectationJ G β J {y, g} * sourcePairDisconnSum G β J {y, g} ∅ o g =
        expectationJ G β J {y, g} *
          ∑ S : Finset V, if goodO S then left S else 0 := by rw [hdelta]
    _ ≥ ∑ S : Finset V, if goodO S then target S else 0 := hclaimSum
    _ = gatedSourcePairSum G β J ∅ ∅
          (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) :=
      hmiddle.symm
    _ = isingDeltaSelfLowerMass G β J o y g :=
      middlePairSum_partition_g_self G β J o y g



theorem ising_delta_bound_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    expectationJ G β J {y, g} * isingDeltaPairSum G β J o x y g ≥
      isingDeltaLowerMass G β J o x y g := by
  let my := expectationJ G β J {y, g}
  let goodO : Finset V → Prop := fun S => y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S
  let goodG : Finset V → Prop := fun S => o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S
  let left : Finset V → ℝ := fun S =>
    gatedSourcePairSum G β J (({o, g} : Finset V) ∆ {x, y}) ∅
      (fun m => notConnComp G m o = S)
  let target : Finset V → ℝ := fun S =>
    gatedSourcePairSum G β J {o, x} ∅
      (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g)
  let atGhost : Finset V → ℝ := fun S =>
    gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m g = S)
  have hsrc : (({o, g} : Finset V) ∆ {x, y}) =
      ({y, g} : Finset V) ∆ {o, x} :=
    deltaSource_comm hox hoy hog hxy hxg hyg
  have hclaimSum :
      (∑ S : Finset V, if goodO S then target S else 0) ≤
        my * ∑ S : Finset V, if goodO S then left S else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    by_cases hgood : goodO S
    · rw [if_pos hgood, if_pos hgood]
      rcases hgood with ⟨hyS, hgS, hoS, hxS⟩
      have hc := claim1_ising_unconditional_cleared G β J hβ hJ
        S o x y g hoS hxS hyS hgS hyg
      change target S ≤ my * left S
      dsimp only [target, left, my]
      rw [hsrc]
      exact hc
    · simp [hgood]
  have hdelta : isingDeltaPairSum G β J o x y g =
      ∑ S : Finset V, if goodO S then left S else 0 := by
    simpa only [goodO, left] using
      isingDeltaPairSum_partition_o G β J hox hoy hog hxy hxg hyg
  have hmiddleO :
      gatedSourcePairSum G β J {o, x} ∅
          (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
        ∑ S : Finset V, if goodO S then target S else 0 := by
    simpa only [goodO, target] using middlePairSum_partition_o G β J hox
  have hmiddleG :
      gatedSourcePairSum G β J {o, x} ∅
          (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) =
        ∑ S : Finset V, if goodG S then atGhost S else 0 := by
    simpa only [goodG, atGhost] using middlePairSum_partition_g G β J hox
  have hclaim2 :
      (∑ S : Finset V, if goodG S then atGhost S else 0) =
        isingDeltaLowerMass G β J o x y g := by
    unfold isingDeltaLowerMass
    apply Finset.sum_congr rfl
    intro S _
    by_cases hgood : goodG S
    · rw [if_pos hgood, if_pos (by simpa only [goodG] using hgood)]
      rcases hgood with ⟨hoS, hxS, hyS, hgS⟩
      dsimp only [atGhost]
      exact claim2_ising_gated G β J S g o x hgS hoS hxS
    · rw [if_neg hgood, if_neg (by simpa only [goodG] using hgood)]
  calc
    expectationJ G β J {y, g} * isingDeltaPairSum G β J o x y g =
        my * ∑ S : Finset V, if goodO S then left S else 0 := by rw [hdelta]
    _ ≥ ∑ S : Finset V, if goodO S then target S else 0 := hclaimSum
    _ = gatedSourcePairSum G β J {o, x} ∅
          (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) := hmiddleO.symm
    _ = ∑ S : Finset V, if goodG S then atGhost S else 0 := hmiddleG
    _ = isingDeltaLowerMass G β J o x y g := hclaim2




theorem ising_delta_bound (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hmy : 0 < expectationJ G β J {y, g}) :
    isingDeltaPairSum G β J o x y g ≥
      (expectationJ G β J {y, g})⁻¹ * isingDeltaLowerMass G β J o x y g := by
  have h := ising_delta_bound_cleared G β J hβ hJ hox hoy hog hxy hxg hyg
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmy.le)
  calc
    (expectationJ G β J {y, g})⁻¹ * isingDeltaLowerMass G β J o x y g ≤
        (expectationJ G β J {y, g})⁻¹ *
          (expectationJ G β J {y, g} * isingDeltaPairSum G β J o x y g) := hm
    _ = isingDeltaPairSum G β J o x y g := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmy), one_mul]

end Sharpness
end StatMech
