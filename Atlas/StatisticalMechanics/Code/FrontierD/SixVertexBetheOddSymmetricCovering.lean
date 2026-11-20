/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricAnalytic
import Code.FrontierD.SixVertexBetheSymmetricCovering





open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexOddPositiveHalfProjection (m : Nat) :
    (Fin ((m + 1) + m) → Real) →L[Real] (Fin m → Real) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (sixVertexOddPositiveIndex m j)

@[simp] theorem sixVertexOddPositiveHalfProjection_apply
    (m : Nat) (p : Fin ((m + 1) + m) → Real) (j : Fin m) :
    sixVertexOddPositiveHalfProjection m p j =
      p (sixVertexOddPositiveIndex m j) := rfl

@[simp] theorem sixVertexOddPositiveHalfProjection_lift
    (m : Nat) (q : Fin m → Real) :
    sixVertexOddPositiveHalfProjection m (sixVertexOddSymmetricLift m q) = q := by
  funext j
  simp

theorem sixVertexOddSymmetricLift_projection
    (m : Nat) {p : Fin ((m + 1) + m) → Real}
    (hp : SixVertexRootSymmetric p) :
    sixVertexOddSymmetricLift m (sixVertexOddPositiveHalfProjection m p) = p := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · refine Fin.lastCases ?_ ?_ j
    · have hs := hp (sixVertexOddCentralIndex m)
      rw [sixVertexOddCentralIndex_rev] at hs
      rw [show Fin.castAdd m (Fin.last m) = sixVertexOddCentralIndex m by rfl,
        sixVertexOddSymmetricLift_central]
      linarith
    · intro k
      rw [show Fin.castAdd m k.castSucc = sixVertexOddNegativeIndex m k by rfl,
        sixVertexOddSymmetricLift_negative]
      have hs := hp (sixVertexOddPositiveIndex m k.rev)
      rw [sixVertexOddPositiveIndex_rev] at hs
      simpa only [Fin.rev_rev, sixVertexOddPositiveHalfProjection_apply] using hs.symm
  · rw [show Fin.natAdd (m + 1) j = sixVertexOddPositiveIndex m j by rfl,
      sixVertexOddSymmetricLift_positive]
    rfl



theorem isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_oddSymmetricJacobian
    {a b : Real} (ha : 2 < a) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * ((m + 1) + m) ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m)))
    (hjac : ∀ z ∈ C, Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2))) :
    IsLocalHomeomorphOn
      (@sixVertexBetheContinuationProjection a b N ((m + 1) + m)) C := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro z hzC
  let c : Real := z.1.1
  let p : Fin ((m + 1) + m) → Real := z.1.2
  let q : Fin m → Real := sixVertexOddPositiveHalfProjection m p
  have hcIcc : c ∈ Set.Icc a b := z.2.1
  have hc : 2 < c := ha.trans_le hcIcc.1
  have hpclosed : SixVertexClosedRootSimplex p := z.2.2.1
  have hpfix : sixVertexBetheUpdate c N ((m + 1) + m) p = p := z.2.2.2
  have hpsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) p :=
    (sixVertexBetheUpdate_eq_self_iff hN p).mp hpfix
  have hpopen : SixVertexOpenRootSimplex p :=
    sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hpclosed hpfix
  have hlift : sixVertexOddSymmetricLift m q = p :=
    sixVertexOddSymmetricLift_projection m hpopen.2.1
  have hqsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) := by simpa [hlift] using hpsol
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticOddSymmetricBetheBranch hc hqsol
    (hjac z hzC)
  obtain ⟨A, hA_sub, hA_open, hqA⟩ := mem_nhds_iff.mp B.eventually_unique
  have hroot_cont : ContinuousAt B.roots c := B.analyticAt_roots.continuousAt
  have hgraph_tendsto : Tendsto (fun t => (t, B.roots t))
      (nhds c) (nhds (c, q)) := by
    have h := continuousAt_id.prodMk hroot_cont
    change Tendsto (fun t => (t, B.roots t)) (nhds c)
      (nhds (c, B.roots c)) at h
    rwa [B.roots_at] at h
  have hgraphA : ∀ᶠ t in nhds c, (t, B.roots t) ∈ A :=
    hgraph_tendsto.eventually (hA_open.mem_nhds hqA)
  let D : Set (Fin ((m + 1) + m) → Real) :=
    {r | StrictMono r ∧ SixVertexRootsInOpenInterval r}
  have hD_open : IsOpen D :=
    isOpen_sixVertexNonsymmetricOpenRootDomain ((m + 1) + m)
  have hpD : p ∈ D := ⟨hpopen.1, hpopen.2.2⟩
  have hfull_tendsto : Tendsto
      (fun t => sixVertexOddSymmetricLift m (B.roots t))
      (nhds c) (nhds p) := by
    have hcomp := (sixVertexOddSymmetricLift m).continuous.continuousAt.comp_of_eq
      hroot_cont B.roots_at
    have hcomp' : Tendsto
        (fun t => sixVertexOddSymmetricLift m (B.roots t))
        (nhds c)
        (nhds (sixVertexOddSymmetricLift m (B.roots c))) := hcomp
    rw [B.roots_at, hlift] at hcomp'
    exact hcomp'
  have hrootD : ∀ᶠ t in nhds c,
      sixVertexOddSymmetricLift m (B.roots t) ∈ D :=
    hfull_tendsto.eventually (hD_open.mem_nhds hpD)
  let Good : Real → Prop := fun t =>
    ContinuousAt B.roots t ∧
    SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
      (sixVertexOddSymmetricLift m (B.roots t)) ∧
    sixVertexOddSymmetricLift m (B.roots t) ∈ D ∧
    (t, B.roots t) ∈ A
  have hgood : ∀ᶠ t in nhds c, Good t := by
    filter_upwards [B.analyticAt_roots.eventually_continuousAt,
      B.eventually_solution, hrootD, hgraphA] with t hct hsol hDt hAt
    exact ⟨hct, hsol, hDt, hAt⟩
  obtain ⟨W, hW_sub, hW_open, hcW⟩ := mem_nhds_iff.mp hgood
  let V : Set (Set.Icc a b) := {t | (t.1 : Real) ∈ W}
  have hV_open : IsOpen V := hW_open.preimage continuous_subtype_val
  let U : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m)) :=
    {x | (x.1.1, sixVertexOddPositiveHalfProjection m x.1.2) ∈ A ∧
      x.1.1 ∈ W}
  have hcoord_cont : Continuous
      (fun x : SixVertexBetheContinuationSpace a b N ((m + 1) + m) =>
        (x.1.1, sixVertexOddPositiveHalfProjection m x.1.2)) :=
    continuous_subtype_val.fst.prodMk
      ((sixVertexOddPositiveHalfProjection m).continuous.comp
        continuous_subtype_val.snd)
  have hU_open : IsOpen U :=
    (hA_open.preimage hcoord_cont).inter
      (hW_open.preimage continuous_subtype_val.fst)
  have hzU : z ∈ U := ⟨by simpa [c, q] using hqA, hcW⟩
  have hbranch_mem (t : V) :
      (t.1.1, sixVertexOddSymmetricLift m (B.roots t.1.1)) ∈
        sixVertexBetheContinuationSet a b N ((m + 1) + m) := by
    have htgood := hW_sub t.2
    have htopen : SixVertexOpenRootSimplex
        (sixVertexOddSymmetricLift m (B.roots t.1.1)) :=
      ⟨htgood.2.2.1.1,
        sixVertexOddSymmetricLift_symmetric m (B.roots t.1.1),
        htgood.2.2.1.2⟩
    exact ⟨t.1.2, htopen.toClosed,
      (sixVertexBetheUpdate_eq_self_iff hN _).mpr htgood.2.1⟩
  let e : U ≃ V :=
    { toFun := fun x =>
        ⟨sixVertexBetheContinuationProjection x.1, x.2.2⟩
      invFun := fun t =>
        ⟨⟨(t.1.1, sixVertexOddSymmetricLift m (B.roots t.1.1)),
          hbranch_mem t⟩, by
            refine ⟨?_, t.2⟩
            simpa using (hW_sub t.2).2.2.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hxopen := sixVertexBetheContinuationSet_subset_open ha hhalf x.1.2
          have hxsol : SixVertexSatisfiesBetheEquations
              x.1.1.1 N ((m + 1) + m) x.1.1.2 :=
            (sixVertexBetheUpdate_eq_self_iff hN _).mp x.1.2.2.2
          have hxcoordSol : SixVertexSatisfiesBetheEquations
              x.1.1.1 N ((m + 1) + m)
              (sixVertexOddSymmetricLift m
                (sixVertexOddPositiveHalfProjection m x.1.1.2)) := by
            rw [sixVertexOddSymmetricLift_projection m hxopen.2.1]
            exact hxsol
          have heq := hA_sub x.2.1 hxcoordSol
          have heq' : B.roots x.1.1.1 =
              sixVertexOddPositiveHalfProjection m x.1.1.2 := by
            simpa only using heq
          change sixVertexOddSymmetricLift m (B.roots x.1.1.1) = x.1.1.2
          rw [heq']
          exact sixVertexOddSymmetricLift_projection m hxopen.2.1
      right_inv := by
        intro t
        apply Subtype.ext
        rfl }
  have he_cont : Continuous e :=
    Continuous.subtype_mk
      (continuous_sixVertexBetheContinuationProjection.comp
        continuous_subtype_val) _
  have he_inv_cont : Continuous e.symm := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hrootsV : Continuous (fun t : V => B.roots t.1.1) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ((hW_sub t.2).1.comp_of_eq
        (continuous_subtype_val.comp continuous_subtype_val).continuousAt rfl)
    exact (continuous_subtype_val.comp continuous_subtype_val).prodMk
      ((sixVertexOddSymmetricLift m).continuous.comp hrootsV)
  let E : U ≃ₜ V := Homeomorph.mk e he_cont he_inv_cont
  refine ⟨U, hU_open.mem_nhds hzU, ?_⟩
  have hemb := hV_open.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  simpa [E, e, U, V, sixVertexBetheContinuationProjection,
    Function.comp_def] using hemb

theorem isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian
    {a b : Real} (ha : 2 < a) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * ((m + 1) + m) ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m)))
    (hC : IsOpen C)
    (hjac : ∀ z ∈ C, Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2))) :
    IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
  have hOn :=
    isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_oddSymmetricJacobian
      ha hN hhalf C hjac
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hsub : IsLocalHomeomorphOn
      (Subtype.val : C →
        SixVertexBetheContinuationSpace a b N ((m + 1) + m)) Set.univ :=
    hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp := hOn.comp hsub (fun z _ => z.2)
  simpa [sixVertexBetheContinuationProjectionOn, Function.comp_def] using hcomp

end

end StatMech.FrontierD
