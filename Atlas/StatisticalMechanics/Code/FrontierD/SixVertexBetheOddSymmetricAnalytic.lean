/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricAnalytic








open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexOddSymmetricLiftLinearMap (m : Nat) :
    (Fin m → Real) →ₗ[Real] (Fin ((m + 1) + m) → Real) where
  toFun q := Fin.addCases
    (Fin.lastCases 0 (fun i => -q i.rev)) q
  map_add' q r := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · simp
      · intro k
        simp [add_comm]
    · simp
  map_smul' a q := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · simp
      · intro k
        simp
    · simp

def sixVertexOddSymmetricLift (m : Nat) :
    (Fin m → Real) →L[Real] (Fin ((m + 1) + m) → Real) :=
  (sixVertexOddSymmetricLiftLinearMap m).toContinuousLinearMap

def sixVertexOddNegativeIndex (m : Nat) (j : Fin m) : Fin ((m + 1) + m) :=
  Fin.castAdd m j.castSucc

def sixVertexOddCentralIndex (m : Nat) : Fin ((m + 1) + m) :=
  Fin.castAdd m (Fin.last m)

def sixVertexOddPositiveIndex (m : Nat) (j : Fin m) : Fin ((m + 1) + m) :=
  Fin.natAdd (m + 1) j

@[simp] theorem sixVertexOddSymmetricLift_negative
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q (sixVertexOddNegativeIndex m j) =
      -q j.rev := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddNegativeIndex]

@[simp] theorem sixVertexOddSymmetricLift_central
    (m : Nat) (q : Fin m → Real) :
    sixVertexOddSymmetricLift m q (sixVertexOddCentralIndex m) = 0 := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddCentralIndex]

@[simp] theorem sixVertexOddSymmetricLift_positive
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q (sixVertexOddPositiveIndex m j) = q j := by
  simp [sixVertexOddSymmetricLift, sixVertexOddSymmetricLiftLinearMap,
    sixVertexOddPositiveIndex]

theorem sixVertexOddNegativeIndex_rev
    (m : Nat) (j : Fin m) :
    (sixVertexOddNegativeIndex m j).rev =
      sixVertexOddPositiveIndex m j.rev := by
  apply Fin.ext
  simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex,
    Fin.rev, Fin.castAdd, Fin.natAdd]
  omega

theorem sixVertexOddCentralIndex_rev (m : Nat) :
    (sixVertexOddCentralIndex m).rev = sixVertexOddCentralIndex m := by
  apply Fin.ext
  simp [sixVertexOddCentralIndex, Fin.rev, Fin.castAdd]

theorem sixVertexOddPositiveIndex_rev
    (m : Nat) (j : Fin m) :
    (sixVertexOddPositiveIndex m j).rev =
      sixVertexOddNegativeIndex m j.rev := by
  apply Fin.ext
  simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex,
    Fin.rev, Fin.castAdd, Fin.natAdd]
  omega

theorem sixVertexOddSymmetricLift_symmetric
    (m : Nat) (q : Fin m → Real) :
    SixVertexRootSymmetric (sixVertexOddSymmetricLift m q) := by
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · refine Fin.lastCases ?_ ?_ j
    · rw [show Fin.castAdd m (Fin.last m) = sixVertexOddCentralIndex m by rfl,
        sixVertexOddCentralIndex_rev]
      simp
    · intro k
      rw [show Fin.castAdd m k.castSucc = sixVertexOddNegativeIndex m k by rfl,
        sixVertexOddNegativeIndex_rev]
      simp
  · rw [show Fin.natAdd (m + 1) j = sixVertexOddPositiveIndex m j by rfl,
      sixVertexOddPositiveIndex_rev]
    simp

theorem sixVertexOddSymmetricLift_injective (m : Nat) :
    Function.Injective (sixVertexOddSymmetricLift m) := by
  intro q r h
  funext j
  have := congrFun h (sixVertexOddPositiveIndex m j)
  simpa using this

def sixVertexOddSymmetricBetheResidual
    (N m : Nat) (c : Real) (q : Fin m → Real) : Fin m → Real :=
  fun j => sixVertexBetheResidual c N ((m + 1) + m)
    (sixVertexOddSymmetricLift m q) (sixVertexOddPositiveIndex m j)

def sixVertexOddSymmetricBetheResidualGraph (N m : Nat) :
    (Real × (Fin m → Real)) → (Real × (Fin m → Real)) :=
  fun q => (q.1, sixVertexOddSymmetricBetheResidual N m q.1 q.2)

theorem analyticAt_sixVertexOddSymmetricBetheResidual_family
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        sixVertexOddSymmetricBetheResidual N m z.1 z.2) q := by
  let liftPair : (Real × (Fin m → Real)) →L[Real]
      (Real × (Fin ((m + 1) + m) → Real)) :=
    (ContinuousLinearMap.fst Real Real (Fin m → Real)).prod
      ((sixVertexOddSymmetricLift m).comp
        (ContinuousLinearMap.snd Real Real (Fin m → Real)))
  let positive : (Fin ((m + 1) + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (sixVertexOddPositiveIndex m j)
  have hfull : AnalyticAt Real
      (fun z : Real × (Fin ((m + 1) + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N ((m + 1) + m) z.2 j)
      (q.1, sixVertexOddSymmetricLift m q.2) :=
    analyticAt_sixVertexBetheResidual_family N ((m + 1) + m)
      (q.1, sixVertexOddSymmetricLift m q.2) hc
  have hlift : AnalyticAt Real (liftPair :
      (Real × (Fin m → Real)) →
        (Real × (Fin ((m + 1) + m) → Real))) q := liftPair.analyticAt q
  have hcomp : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin ((m + 1) + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N ((m + 1) + m) w.2 j)
            (liftPair z)) q :=
    hfull.comp (f := fun z => liftPair z) (x := q) hlift
  have hpositive := positive.analyticAt
    ((fun w : Real × (Fin ((m + 1) + m) → Real) =>
      fun j => sixVertexBetheResidual w.1 N ((m + 1) + m) w.2 j)
        (liftPair q))
  have hout := hpositive.comp hcomp
  simpa [liftPair, positive, sixVertexOddSymmetricBetheResidual,
    sixVertexOddPositiveIndex, Function.comp_def] using hout

theorem analyticAt_sixVertexOddSymmetricBetheResidualGraph
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexOddSymmetricBetheResidualGraph N m) q :=
  analyticAt_fst.prod
    (analyticAt_sixVertexOddSymmetricBetheResidual_family N m q hc)

def sixVertexOddSymmetricBetheRootJacobian
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    (Fin m → Real) →L[Real] (Fin m → Real) :=
  fderiv Real (sixVertexOddSymmetricBetheResidual N m c) q

theorem sixVertexOddSymmetricBetheResidual_eq_zero_iff
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexOddSymmetricBetheResidual N m c q = 0 ↔
      SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
        (sixVertexOddSymmetricLift m q) := by
  constructor
  · intro h
    apply (sixVertexBetheResidual_eq_zero_iff c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).1
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexOddSymmetricLift_symmetric m q)
          (sixVertexOddCentralIndex m)
        rw [sixVertexOddCentralIndex_rev] at hsymm
        have hscalar : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) =
          -sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) := by
          simpa only using hsymm
        change sixVertexBetheResidual c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (sixVertexOddCentralIndex m) = 0
        linarith
      · intro k
        have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexOddSymmetricLift_symmetric m q)
          (sixVertexOddPositiveIndex m k.rev)
        have hzero : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q)
            (sixVertexOddPositiveIndex m k.rev) = 0 := by
          simpa [sixVertexOddSymmetricBetheResidual] using congrFun h k.rev
        rw [sixVertexOddPositiveIndex_rev] at hsymm
        have hrel : sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (sixVertexOddNegativeIndex m k) =
          -sixVertexBetheResidual c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q)
              (sixVertexOddPositiveIndex m k.rev) := by
          simpa only [Fin.rev_rev] using hsymm
        change sixVertexBetheResidual c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (sixVertexOddNegativeIndex m k) = 0
        rw [hrel, hzero, neg_zero]
    · simpa [sixVertexOddSymmetricBetheResidual,
        sixVertexOddPositiveIndex] using congrFun h j
  · intro h
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).2 h (sixVertexOddPositiveIndex m j)

structure SixVertexLocalAnalyticOddSymmetricBetheBranch
    (N m : Nat) (c : Real) (q : Fin m → Real) where
  roots : Real → (Fin m → Real)
  analyticAt_roots : AnalyticAt Real roots c
  roots_at : roots c = q
  eventually_solution : ∀ᶠ t in nhds c,
    SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
      (sixVertexOddSymmetricLift m (roots t))
  eventually_unique : ∀ᶠ z : Real × (Fin m → Real) in nhds (c, q),
    SixVertexSatisfiesBetheEquations z.1 N ((m + 1) + m)
      (sixVertexOddSymmetricLift m z.2) → roots z.1 = z.2

theorem sixVertexOddSymmetricBetheResidualGraph_fderiv_injective
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hjac : Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
    Function.Injective
      (fderiv Real (sixVertexOddSymmetricBetheResidualGraph N m) (c, q)) := by
  let H := sixVertexOddSymmetricBetheResidualGraph N m
  let L := fderiv Real H (c, q)
  let J := sixVertexOddSymmetricBetheRootJacobian N m c q
  have hH : HasFDerivAt H L (c, q) :=
    (analyticAt_sixVertexOddSymmetricBetheResidualGraph N m (c, q) hc)
      |>.hasStrictFDerivAt.hasFDerivAt
  let incl : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) :=
    (0 : (Fin m → Real) →L[Real] Real).prod
      (ContinuousLinearMap.id Real (Fin m → Real))
  have hincl : HasFDerivAt (fun r : Fin m → Real => (c, r)) incl q :=
    (hasFDerivAt_const c q).prodMk (hasFDerivAt_id q)
  have hcomp : HasFDerivAt (fun r : Fin m → Real => H (c, r))
      (L.comp incl) q := hH.comp q hincl
  have hres : HasFDerivAt
      (sixVertexOddSymmetricBetheResidual N m c) J q :=
    (analyticAt_sixVertexOddSymmetricBetheResidual_family N m (c, q) hc)
      |>.comp (x := q) (f := fun r : Fin m → Real => (c, r))
        (analyticAt_const.prod analyticAt_id)
      |>.hasStrictFDerivAt.hasFDerivAt
  let direct : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) :=
    (0 : (Fin m → Real) →L[Real] Real).prod J
  have hdirect : HasFDerivAt (fun r : Fin m → Real => H (c, r))
      direct q := (hasFDerivAt_const c q).prodMk hres
  have hderiv : L.comp incl = direct := hcomp.unique hdirect
  intro z w hzw
  let u := z - w
  have hu : L u = 0 := by
    dsimp [u, L]
    rw [map_sub, hzw, sub_self]
  have hfst : u.1 = 0 := by
    have hproj : HasFDerivAt
        (fun z : Real × (Fin m → Real) => z.1)
        (ContinuousLinearMap.fst Real Real (Fin m → Real)) (c, q) :=
      (ContinuousLinearMap.fst Real Real (Fin m → Real)).hasFDerivAt
    have hcompFst : HasFDerivAt
        (fun z : Real × (Fin m → Real) => z.1)
        ((ContinuousLinearMap.fst Real Real (Fin m → Real)).comp L) (c, q) := by
      simpa [H, sixVertexOddSymmetricBetheResidualGraph] using
        ((ContinuousLinearMap.fst Real Real (Fin m → Real)).hasFDerivAt.comp
          (c, q) hH)
    have hfstL :
        (ContinuousLinearMap.fst Real Real (Fin m → Real)).comp L =
          ContinuousLinearMap.fst Real Real (Fin m → Real) :=
      hcompFst.unique hproj
    have h := congrArg
      (fun T : (Real × (Fin m → Real)) →L[Real] Real => T u) hfstL
    simpa [hu] using h.symm
  have hupair : u = (0, u.2) := Prod.ext hfst rfl
  have hJzero : J u.2 = 0 := by
    have happly := congrArg
      (fun T : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) => T u.2)
      hderiv
    have hLzero : L (incl u.2) = 0 := by
      rw [show incl u.2 = u by rw [hupair]; rfl]
      exact hu
    simpa [hLzero, direct] using (congrArg Prod.snd happly).symm
  have hu2 : u.2 = 0 := hjac (by simpa using hJzero)
  have hsub : z - w = 0 := by
    change u = 0
    exact Prod.ext hfst hu2
  exact sub_eq_zero.mp hsub

theorem exists_sixVertexLocalAnalyticOddSymmetricBetheBranch
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    (hjac : Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m c q)) :
    Nonempty (SixVertexLocalAnalyticOddSymmetricBetheBranch N m c q) := by
  let q₀ : Real × (Fin m → Real) := (c, q)
  let H := sixVertexOddSymmetricBetheResidualGraph N m
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexOddSymmetricBetheResidualGraph N m q₀ hc
  have hLinj : Function.Injective L :=
    sixVertexOddSymmetricBetheResidualGraph_fderiv_injective hc hjac
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hLinj
  let e : (Real × (Fin m → Real)) ≃L[Real] (Real × (Fin m → Real)) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × (Fin m → Real)) →L[Real]
        (Real × (Fin m → Real))) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph
      (Real × (Fin m → Real)) (Real × (Fin m → Real)) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have hzero : sixVertexOddSymmetricBetheResidual N m c q = 0 :=
    (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m c q).2 hsol
  have hHq₀ : H q₀ = (c, (0 : Fin m → Real)) := by
    apply Prod.ext
    · rfl
    · simpa [H, q₀, sixVertexOddSymmetricBetheResidualGraph] using hzero
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  let roots : Real → (Fin m → Real) :=
    fun t => (R.symm (t, (0 : Fin m → Real))).2
  have hroots : AnalyticAt Real roots c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real
        (fun t : Real => (t, (0 : Fin m → Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Fin m → Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Fin m → Real))) (x := c) hinput
    have hsnd := analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  have hrootsAt : roots c = q := by
    have hleft := R.left_inv hqsource
    have hinv : R.symm (c, (0 : Fin m → Real)) = (c, q) := by
      rw [← hHq₀]
      simpa [R, q₀] using hleft
    exact congrArg Prod.snd hinv
  have hright := hHe.eventually_right_inverse
  have hinput : Tendsto (fun t : Real => (t, (0 : Fin m → Real)))
      (nhds c) (nhds (H q₀)) := by
    rw [hHq₀]
    exact continuousAt_id.prodMk continuousAt_const
  have hbranchEq : ∀ᶠ t in nhds c,
      H (R.symm (t, (0 : Fin m → Real))) =
        (t, (0 : Fin m → Real)) := hinput.eventually hright
  have hsolution : ∀ᶠ t in nhds c,
      SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
        (sixVertexOddSymmetricLift m (roots t)) := by
    filter_upwards [hbranchEq] with t ht
    apply (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m t (roots t)).1
    have hfst := congrArg Prod.fst ht
    have hsnd := congrArg Prod.snd ht
    change (R.symm (t, (0 : Fin m → Real))).1 = t at hfst
    change sixVertexOddSymmetricBetheResidual N m
      (R.symm (t, (0 : Fin m → Real))).1
      (R.symm (t, (0 : Fin m → Real))).2 = 0 at hsnd
    rw [hfst] at hsnd
    simpa [roots] using hsnd
  have hsource : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      z ∈ R.source := R.open_source.mem_nhds hqsource
  have hunique : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      SixVertexSatisfiesBetheEquations z.1 N ((m + 1) + m)
        (sixVertexOddSymmetricLift m z.2) → roots z.1 = z.2 := by
    filter_upwards [hsource] with z hz hzsol
    have hzres : sixVertexOddSymmetricBetheResidual N m z.1 z.2 = 0 :=
      (sixVertexOddSymmetricBetheResidual_eq_zero_iff N m z.1 z.2).2 hzsol
    have hHz : H z = (z.1, (0 : Fin m → Real)) := by
      apply Prod.ext
      · rfl
      · simpa [H, sixVertexOddSymmetricBetheResidualGraph] using hzres
    have hleft := R.left_inv hz
    have hinv : R.symm (z.1, (0 : Fin m → Real)) = z := by
      rw [← hHz]
      simpa [R] using hleft
    exact congrArg Prod.snd hinv
  exact ⟨{
    roots := roots
    analyticAt_roots := hroots
    roots_at := hrootsAt
    eventually_solution := hsolution
    eventually_unique := by simpa [q₀] using hunique
  }⟩

end
end StatMech.FrontierD
