/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopTwoPointAudit
import Code.Sharpness.HighTempSwitching











open scoped BigOperators symmDiff
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def onsDefectEdgeGraph (u v : V) : SimpleGraph V := G ⊔ SimpleGraph.edge u v

noncomputable instance onsDefectEdgeGraph_decidableAdj (u v : V) :
    DecidableRel (onsDefectEdgeGraph G u v).Adj := Classical.decRel _



noncomputable def ons_defectEdgeX (u v : V) (x z : Real) : Real :=
  let e := s(u, v)
  ∑ F ∈ (insert e G.edgeFinset).powerset.filter IsEvenSubgraph,
    (if e ∈ F then z else 1) * x ^ (F.erase e).card

theorem insert_defect_hasOddBoundary_iff
    {u v : V} (huv : u ≠ v) {F : Finset (Sym2 V)}
    (heF : s(u, v) ∉ F) :
    HasOddBoundary (insert s(u, v) F) ∅ ↔ HasOddBoundary F {u, v} := by
  have hsingle : HasOddBoundary ({s(u, v)} : Finset (Sym2 V)) {u, v} := by
    simpa [sourcePair_eq_pair huv] using
      (hasOddBoundary_singleton_sourcePair (V := V) huv)
  have hinsert : insert s(u, v) F = F ∆ {s(u, v)} := by
    ext e
    rw [Finset.mem_insert, mem_symmDiff_singleton_iff]
    by_cases he : e = s(u, v)
    · subst e; simp [heF]
    · simp [he]
  constructor
  · intro hEven
    have ht := hasOddBoundary_symmDiff hEven hsingle
    have hrecover : (insert s(u, v) F) ∆ {s(u, v)} = F := by
      rw [hinsert]
      simp
    rw [hrecover] at ht
    convert ht using 1 <;> ext x <;> simp [Finset.mem_symmDiff]
  · intro hsource
    rw [hinsert]
    have ht := hasOddBoundary_symmDiff hsource hsingle
    simpa using ht


theorem ons_defectEdgeX_eq
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v) (x z : Real) :
    ons_defectEdgeX G u v x z = ons_X G x + z * ons_sourceX G {u, v} x := by
  classical
  have heG : s(u, v) ∉ G.edgeFinset := by
    simpa [SimpleGraph.mem_edgeFinset] using hnotAdj
  rw [ons_defectEdgeX]
  rw [Finset.sum_filter]
  let oldEven : Finset (Finset (Sym2 V)) :=
    G.edgeFinset.powerset.filter IsEvenSubgraph
  let oldSource : Finset (Finset (Sym2 V)) :=
    G.edgeFinset.powerset.filter (fun F => HasOddBoundary F {u, v})
  have hsplit :
      (∑ F ∈ (insert s(u, v) G.edgeFinset).powerset,
        if IsEvenSubgraph F then
          (if s(u, v) ∈ F then z else 1) * x ^ (F.erase s(u, v)).card
        else 0) =
      (∑ F ∈ oldEven, x ^ F.card) +
        z * ∑ F ∈ oldSource, x ^ F.card := by
    dsimp only [oldEven, oldSource]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
      Finset.sum_powerset_insert heG]
    apply congrArg₂ (fun a b : Real => a + b)
    · apply Finset.sum_congr rfl
      intro F hF
      have heF : s(u, v) ∉ F :=
        Finset.notMem_of_mem_powerset_of_notMem hF heG
      simp [heF]
    · apply Finset.sum_congr rfl
      intro F hF
      have heF : s(u, v) ∉ F :=
        Finset.notMem_of_mem_powerset_of_notMem hF heG
      have hboundary :
          IsEvenSubgraph (insert s(u, v) F) ↔ HasOddBoundary F {u, v} := by
        rw [← hasOddBoundary_empty]
        exact insert_defect_hasOddBoundary_iff (V := V) huv heF
      by_cases hsource : HasOddBoundary F {u, v}
      · simp [hboundary.mpr hsource, hsource, heF]
      · simp [hsource, hboundary.not.mpr hsource]
  rw [hsplit]
  rfl



theorem hasDerivAt_ons_defectEdgeX
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v) (x z : Real) :
    HasDerivAt (ons_defectEdgeX G u v x) (ons_sourceX G {u, v} x) z := by
  have heq : ons_defectEdgeX G u v x =
      fun w => ons_X G x + w * ons_sourceX G {u, v} x := by
    funext w
    exact ons_defectEdgeX_eq G huv hnotAdj x w
  rw [heq]
  convert (hasDerivAt_const (x := z) (ons_X G x)).add
    ((hasDerivAt_id z).mul_const (ons_sourceX G {u, v} x)) using 1 <;> ring



noncomputable def ons_disorderX (Q : Finset (Sym2 V)) (x : Real) : Real :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ (H ∆ Q).card



theorem ons_sourceX_eq_disorderX
    {u v : V} {Q : Finset (Sym2 V)}
    (hQsub : Q ⊆ G.edgeFinset) (hQ : HasOddBoundary Q {u, v}) (x : Real) :
    ons_sourceX G {u, v} x = ons_disorderX G Q x := by
  classical
  unfold ons_sourceX ons_disorderX
  apply Finset.sum_bij (fun F _ => F ∆ Q)
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_powerset] at hF ⊢
    refine ⟨?_, ?_⟩
    · intro e he
      rw [Finset.mem_symmDiff] at he
      exact he.elim (fun h => hF.1 h.1) (fun h => hQsub h.1)
    · rw [← hasOddBoundary_empty]
      have ht := hasOddBoundary_symmDiff hF.2 hQ
      simpa using ht
  · intro F hF H hH hEq
    calc
      F = (F ∆ Q) ∆ Q := by simp [symmDiff_assoc]
      _ = (H ∆ Q) ∆ Q := by rw [hEq]
      _ = H := by simp [symmDiff_assoc]
  · intro H hH
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    let F := H ∆ Q
    have hFsub : F ⊆ G.edgeFinset := by
      intro e he
      rw [Finset.mem_symmDiff] at he
      exact he.elim (fun h => hH.1 h.1) (fun h => hQsub h.1)
    have hFsource : HasOddBoundary F {u, v} := by
      have hEven : HasOddBoundary H ∅ := (hasOddBoundary_empty H).2 hH.2
      have ht := hasOddBoundary_symmDiff hEven hQ
      change HasOddBoundary F (∅ ∆ {u, v}) at ht
      convert ht using 1
      ext w
      simp [Finset.mem_symmDiff]
    refine ⟨F, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hFsub, hFsource⟩
    · dsimp only [F]
      simp [symmDiff_assoc]
  · intro F hF
    simp [symmDiff_assoc]

end StatMech.Onsager
