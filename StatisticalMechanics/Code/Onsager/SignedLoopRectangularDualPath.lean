/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Onsager.SignedLoopDisorderKacWard
import Code.Onsager.SignedLoopCriticalWeight

open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section


abbrev ons_RectDualVertex (M N : Nat) := Fin (M + 1) × Fin (N + 1)


def ons_rectDualAdj (M N : Nat) (u v : ons_RectDualVertex M N) : Prop :=
  (u.2 = v.2 ∧ Nat.dist u.1.val v.1.val = 1) ∨
    (u.1 = v.1 ∧ Nat.dist u.2.val v.2.val = 1)

instance (M N : Nat) : DecidableRel (ons_rectDualAdj M N) := by
  intro u v
  unfold ons_rectDualAdj
  infer_instance


def ons_rectDualGraph (M N : Nat) : SimpleGraph (ons_RectDualVertex M N) where
  Adj := ons_rectDualAdj M N
  symm := by
    intro u v
    rintro (⟨hcoord, hdist⟩ | ⟨hcoord, hdist⟩)
    · exact Or.inl ⟨hcoord.symm, by simpa [Nat.dist_comm] using hdist⟩
    · exact Or.inr ⟨hcoord.symm, by simpa [Nat.dist_comm] using hdist⟩
  loopless := ⟨by
    intro u
    rintro (⟨_, hdist⟩ | ⟨_, hdist⟩) <;>
      simp at hdist⟩

instance (M N : Nat) : DecidableRel (ons_rectDualGraph M N).Adj :=
  inferInstanceAs (DecidableRel (ons_rectDualAdj M N))


structure ons_RectDualPath (M N : Nat) where
  source : ons_RectDualVertex M N
  target : ons_RectDualVertex M N
  source_ne_target : source ≠ target
  walk : (ons_rectDualGraph M N).Walk source target
  isPath : walk.IsPath


def ons_rectDualPathDefect {M N : Nat} (path : ons_RectDualPath M N) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  path.walk.edges.toFinset

theorem ons_rectDualPathDefect_subset_edgeFinset
    {M N : Nat} (path : ons_RectDualPath M N) :
    ons_rectDualPathDefect path ⊆ (ons_rectDualGraph M N).edgeFinset := by
  intro edge hedge
  obtain ⟨⟨u, v⟩, huv⟩ := edge.exists_rep
  rw [← huv] at hedge ⊢
  rw [SimpleGraph.mem_edgeFinset]
  exact path.walk.adj_of_mem_edges
    (by simpa [ons_rectDualPathDefect] using hedge)



theorem ons_rectDualPathDefect_hasOddBoundary
    {M N : Nat} (path : ons_RectDualPath M N) :
    HasOddBoundary (ons_rectDualPathDefect path) {path.source, path.target} := by
  have hboundary := hasOddBoundary_path_edges path.walk path.isPath
  rw [sourcePair_eq_pair path.source_ne_target] at hboundary
  exact hboundary


def ons_rectDualPathDefectWeight {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real)
    (edge : Sym2 (ons_RectDualVertex M N)) : Complex :=
  if edge ∈ ons_rectDualPathDefect path then (x : Complex)⁻¹ else (x : Complex)

@[simp] theorem ons_rectDualPathDefectWeight_of_mem
    {M N : Nat} (path : ons_RectDualPath M N) (x : Real)
    {edge : Sym2 (ons_RectDualVertex M N)}
    (hedge : edge ∈ ons_rectDualPathDefect path) :
    ons_rectDualPathDefectWeight path x edge = (x : Complex)⁻¹ := by
  simp [ons_rectDualPathDefectWeight, hedge]

@[simp] theorem ons_rectDualPathDefectWeight_of_not_mem
    {M N : Nat} (path : ons_RectDualPath M N) (x : Real)
    {edge : Sym2 (ons_RectDualVertex M N)}
    (hedge : edge ∉ ons_rectDualPathDefect path) :
    ons_rectDualPathDefectWeight path x edge = (x : Complex) := by
  simp [ons_rectDualPathDefectWeight, hedge]



def ons_rectDualPathDefectKWDet {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  (1 - kwGraphTransition (ons_rectDualGraph M N)
    (ons_rectDualPathDefectWeight path x) embedding.turnPhase).det


def ons_rectDualKWDet {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (x : Real) : Complex :=
  (1 - kwGraphTransition (ons_rectDualGraph M N)
    (fun _ => (x : Complex)) embedding.turnPhase).det



theorem coe_ons_rectDual_X_sq_eq_kwDet
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (x : Real) :
    (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 =
      ons_rectDualKWDet embedding x := by
  rw [ons_rectDualKWDet,
    kacWard_straightLine_arbitrary_adaptive]
  congr 1
  unfold ons_X kwEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro edges _
  simp [Finset.prod_const]



def ons_rectDualPathSignedLoopObservable {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target} x : Complex) ^ 2 /
    (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card)


theorem coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    (ons_sourceX (ons_rectDualGraph M N)
        {path.source, path.target} x : Complex) ^ 2 =
      (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path x := by
  exact coe_ons_sourceX_sq_eq_defect_kwDet
    (ons_rectDualGraph M N) embedding
    (ons_rectDualPathDefect_subset_edgeFinset path)
    (ons_rectDualPathDefect_hasOddBoundary path) hx



theorem ons_rectDualPath_defectKWDet_eq_signedLoopObservable
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    ons_rectDualPathDefectKWDet embedding path x =
      ons_rectDualPathSignedLoopObservable path x := by
  have hraw := coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    embedding path hx
  have hxc : (x : Complex) ≠ 0 := by exact_mod_cast hx
  unfold ons_rectDualPathSignedLoopObservable
  rw [hraw]
  field_simp [hxc]



theorem coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) {beta : Real} (hbeta : 0 < beta) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((Real.tanh beta : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path (Real.tanh beta)) /
        ons_rectDualKWDet embedding (Real.tanh beta) := by
  have htanh : Real.tanh beta ≠ 0 := by
    intro hzero
    apply hbeta.ne'
    calc
      beta = Real.artanh (Real.tanh beta) := (Real.artanh_tanh beta).symm
      _ = Real.artanh 0 := by rw [hzero]
      _ = 0 := by simp
  rw [ons_finiteTwoPoint_highTemp_ratio
    (ons_rectDualGraph M N) beta path.source_ne_target]
  push_cast
  rw [← Complex.ofReal_tanh]
  rw [div_pow,
    coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet embedding path htanh,
    coe_ons_rectDual_X_sq_eq_kwDet embedding]


theorem coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((ons_signedLoopCriticalWeight : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathDefectKWDet embedding path
          ons_signedLoopCriticalWeight) /
        ons_rectDualKWDet embedding ons_signedLoopCriticalWeight := by
  simpa [tanh_ons_betaC] using
    (coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
      embedding path ons_betaC_pos)



theorem ons_rectDualPath_critical_defectKWDet_eq_signedLoopObservable
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ons_rectDualPathDefectKWDet embedding path ons_signedLoopCriticalWeight =
      ons_rectDualPathSignedLoopObservable path ons_signedLoopCriticalWeight :=
  ons_rectDualPath_defectKWDet_eq_signedLoopObservable embedding path
    ons_signedLoopCriticalWeight_pos.ne'

end


end StatMech.Onsager
