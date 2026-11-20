/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricJacobian










open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenPositiveHalfProjection (m : Nat) :
    (Fin (m + m) → Real) →L[Real] (Fin m → Real) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd m j)

@[simp] theorem sixVertexEvenPositiveHalfProjection_apply
    (m : Nat) (p : Fin (m + m) → Real) (j : Fin m) :
    sixVertexEvenPositiveHalfProjection m p j = p (Fin.natAdd m j) := rfl

@[simp] theorem sixVertexEvenPositiveHalfProjection_lift
    (m : Nat) (q : Fin m → Real) :
    sixVertexEvenPositiveHalfProjection m (sixVertexEvenSymmetricLift m q) = q := by
  funext j
  rw [sixVertexEvenPositiveHalfProjection_apply,
    sixVertexEvenSymmetricLift_natAdd]

theorem sixVertexEvenSymmetricLift_projection
    (m : Nat) {p : Fin (m + m) → Real}
    (hp : SixVertexRootSymmetric p) :
    sixVertexEvenSymmetricLift m (sixVertexEvenPositiveHalfProjection m p) = p := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · rw [sixVertexEvenSymmetricLift_castAdd]
    have hrev : (Fin.natAdd m j.rev).rev = Fin.castAdd m j := by
      apply Fin.ext
      simp [Fin.rev, Fin.natAdd, Fin.castAdd]
      omega
    have hs := hp (Fin.natAdd m j.rev)
    rw [hrev] at hs
    simpa using hs.symm
  · rw [sixVertexEvenSymmetricLift_natAdd]
    rfl



theorem isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian
    {a b : Real} (ha : 2 < a) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N (m + m)))
    (hjac : ∀ z ∈ C, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2))) :
    IsLocalHomeomorphOn
      (@sixVertexBetheContinuationProjection a b N (m + m)) C := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro z hzC
  let c : Real := z.1.1
  let p : Fin (m + m) → Real := z.1.2
  let q : Fin m → Real := sixVertexEvenPositiveHalfProjection m p
  have hcIcc : c ∈ Set.Icc a b := z.2.1
  have hc : 2 < c := ha.trans_le hcIcc.1
  have hpclosed : SixVertexClosedRootSimplex p := z.2.2.1
  have hpfix : sixVertexBetheUpdate c N (m + m) p = p := z.2.2.2
  have hpsol : SixVertexSatisfiesBetheEquations c N (m + m) p :=
    (sixVertexBetheUpdate_eq_self_iff hN p).mp hpfix
  have hpopen : SixVertexOpenRootSimplex p :=
    sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hpclosed hpfix
  have hlift : sixVertexEvenSymmetricLift m q = p :=
    sixVertexEvenSymmetricLift_projection m hpopen.2.1
  have hqsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q) := by simpa [hlift] using hpsol
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch hc hqsol
    (hjac z hzC)
  obtain ⟨A, hA_sub, hA_open, hqA⟩ := mem_nhds_iff.mp B.eventually_unique
  have hroot_cont : ContinuousAt B.roots c := B.analyticAt_roots.continuousAt
  have hroot_tendsto : Tendsto B.roots (nhds c) (nhds q) := by
    rw [← congrArg nhds B.roots_at]
    exact hroot_cont
  have hgraph_tendsto : Tendsto (fun t => (t, B.roots t))
      (nhds c) (nhds (c, q)) := by
    have h := continuousAt_id.prodMk hroot_cont
    change Tendsto (fun t => (t, B.roots t)) (nhds c)
      (nhds (c, B.roots c)) at h
    rw [B.roots_at] at h
    exact h
  have hgraphA : ∀ᶠ t in nhds c, (t, B.roots t) ∈ A :=
    hgraph_tendsto.eventually (hA_open.mem_nhds hqA)
  let D : Set (Fin (m + m) → Real) :=
    {r | StrictMono r ∧ SixVertexRootsInOpenInterval r}
  have hD_open : IsOpen D := isOpen_sixVertexNonsymmetricOpenRootDomain (m + m)
  have hpD : p ∈ D := ⟨hpopen.1, hpopen.2.2⟩
  have hlift_cont : ContinuousAt
      (fun r : Fin m → Real => sixVertexEvenSymmetricLift m r) q :=
    (sixVertexEvenSymmetricLift m).continuous.continuousAt
  have hfull_tendsto : Tendsto
      (fun t => sixVertexEvenSymmetricLift m (B.roots t))
      (nhds c) (nhds p) := by
    have hcomp := hlift_cont.comp_of_eq hroot_cont B.roots_at
    have hcomp' : Tendsto
        (fun t => sixVertexEvenSymmetricLift m (B.roots t))
        (nhds c) (nhds (sixVertexEvenSymmetricLift m (B.roots c))) := by
      exact hcomp
    rw [B.roots_at] at hcomp'
    rw [hlift] at hcomp'
    exact hcomp'
  have hrootD : ∀ᶠ t in nhds c,
      sixVertexEvenSymmetricLift m (B.roots t) ∈ D :=
    hfull_tendsto.eventually (hD_open.mem_nhds hpD)
  let Good : Real → Prop := fun t =>
    ContinuousAt B.roots t ∧
    SixVertexSatisfiesBetheEquations t N (m + m)
      (sixVertexEvenSymmetricLift m (B.roots t)) ∧
    sixVertexEvenSymmetricLift m (B.roots t) ∈ D ∧
    (t, B.roots t) ∈ A
  have hgood : ∀ᶠ t in nhds c, Good t := by
    filter_upwards [B.analyticAt_roots.eventually_continuousAt,
      B.eventually_solution, hrootD, hgraphA] with t hct hsol hD hA
    exact ⟨hct, hsol, hD, hA⟩
  obtain ⟨W, hW_sub, hW_open, hcW⟩ := mem_nhds_iff.mp hgood
  let V : Set (Set.Icc a b) := {t | (t.1 : Real) ∈ W}
  have hV_open : IsOpen V := hW_open.preimage continuous_subtype_val
  let U : Set (SixVertexBetheContinuationSpace a b N (m + m)) :=
    {x | (x.1.1, sixVertexEvenPositiveHalfProjection m x.1.2) ∈ A ∧
      x.1.1 ∈ W}
  have hcoord_cont : Continuous
      (fun x : SixVertexBetheContinuationSpace a b N (m + m) =>
        (x.1.1, sixVertexEvenPositiveHalfProjection m x.1.2)) := by
    exact continuous_subtype_val.fst.prodMk
      ((sixVertexEvenPositiveHalfProjection m).continuous.comp
        continuous_subtype_val.snd)
  have hU_open : IsOpen U :=
    (hA_open.preimage hcoord_cont).inter
      (hW_open.preimage continuous_subtype_val.fst)
  have hzcoord : (z.1.1, sixVertexEvenPositiveHalfProjection m z.1.2) =
      (c, q) := rfl
  have hzU : z ∈ U := ⟨by simpa [hzcoord] using hqA, hcW⟩
  have hbranch_mem (t : V) :
      (t.1.1, sixVertexEvenSymmetricLift m (B.roots t.1.1)) ∈
        sixVertexBetheContinuationSet a b N (m + m) := by
    have htgood := hW_sub t.2
    have htopen : SixVertexOpenRootSimplex
        (sixVertexEvenSymmetricLift m (B.roots t.1.1)) :=
      ⟨htgood.2.2.1.1,
        sixVertexEvenSymmetricLift_symmetric m (B.roots t.1.1),
        htgood.2.2.1.2⟩
    exact ⟨t.1.2, htopen.toClosed,
      (sixVertexBetheUpdate_eq_self_iff hN _).mpr htgood.2.1⟩
  let e : U ≃ V :=
    { toFun := fun x =>
        ⟨sixVertexBetheContinuationProjection x.1, x.2.2⟩
      invFun := fun t =>
        ⟨⟨(t.1.1, sixVertexEvenSymmetricLift m (B.roots t.1.1)),
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
              x.1.1.1 N (m + m) x.1.1.2 :=
            (sixVertexBetheUpdate_eq_self_iff hN _).mp x.1.2.2.2
          have hxcoordSol : SixVertexSatisfiesBetheEquations
              x.1.1.1 N (m + m)
              (sixVertexEvenSymmetricLift m
                (sixVertexEvenPositiveHalfProjection m x.1.1.2)) := by
            rw [sixVertexEvenSymmetricLift_projection m hxopen.2.1]
            exact hxsol
          have heq := hA_sub x.2.1 hxcoordSol
          have heq' : B.roots x.1.1.1 =
              sixVertexEvenPositiveHalfProjection m x.1.1.2 := by
            simpa only using heq
          change sixVertexEvenSymmetricLift m (B.roots x.1.1.1) = x.1.1.2
          rw [heq']
          exact sixVertexEvenSymmetricLift_projection m hxopen.2.1
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
      ((sixVertexEvenSymmetricLift m).continuous.comp hrootsV)
  let E : U ≃ₜ V := Homeomorph.mk e he_cont he_inv_cont
  refine ⟨U, hU_open.mem_nhds hzU, ?_⟩
  have hemb := hV_open.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  simpa [E, e, U, V, sixVertexBetheContinuationProjection,
    Function.comp_def] using hemb



theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_jacobian
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (hjac : ∀ z ∈ sixVertexBetheContinuationSet a b N (m + m),
      Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1
        (sixVertexEvenPositiveHalfProjection m z.2)))
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
  apply exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph
    ha hab hc₀ hN _ z₀ hz₀
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian
    ha hN hhalf Set.univ (fun z _ => hjac z.1 z.2)

theorem isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian
    {a b : Real} (ha : 2 < a) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N (m + m)))
    (hC : IsOpen C)
    (hjac : ∀ z ∈ C, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2))) :
    IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
  have hOn :=
    isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian
      ha hN hhalf C hjac
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hsub : IsLocalHomeomorphOn
      (Subtype.val : C → SixVertexBetheContinuationSpace a b N (m + m))
      Set.univ :=
    hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp := hOn.comp hsub (fun z _ => z.2)
  simpa [sixVertexBetheContinuationProjectionOn, Function.comp_def] using hcomp



theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_regularComponent
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N (m + m)))
    (hCopen : IsOpen C) (hCcompact : IsCompact C)
    (hjac : ∀ z ∈ C, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) :=
  exists_sixVertexContinuousBetheBranch_of_compactComponent hab hc₀ hN C
    hCcompact
    (isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian
      ha hN hhalf C hCopen hjac)
    z₀ hz₀

end
end StatMech.FrontierD
