/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheLocalAnalytic













open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexEvenSymmetricLiftLinearMap (m : Nat) :
    (Fin m → Real) →ₗ[Real] (Fin (m + m) → Real) where
  toFun q := Fin.addCases (fun i => -q i.rev) q
  map_add' q r := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [add_comm]
  map_smul' a q := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp


def sixVertexEvenSymmetricLift (m : Nat) :
    (Fin m → Real) →L[Real] (Fin (m + m) → Real) :=
  (sixVertexEvenSymmetricLiftLinearMap m).toContinuousLinearMap

@[simp] theorem sixVertexEvenSymmetricLift_castAdd
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricLift m q (Fin.castAdd m j) = -q j.rev := by
  simp [sixVertexEvenSymmetricLift, sixVertexEvenSymmetricLiftLinearMap]

@[simp] theorem sixVertexEvenSymmetricLift_natAdd
    (m : Nat) (q : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricLift m q (Fin.natAdd m j) = q j := by
  simp [sixVertexEvenSymmetricLift, sixVertexEvenSymmetricLiftLinearMap]

theorem sixVertexEvenSymmetricLift_symmetric
    (m : Nat) (q : Fin m → Real) :
    SixVertexRootSymmetric (sixVertexEvenSymmetricLift m q) := by
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · rw [Fin.rev_castAdd]
    have hadd : j.rev.addNat m = Fin.natAdd m j.rev := by
      apply Fin.ext
      simp [Fin.addNat, Fin.natAdd]
      omega
    rw [hadd, sixVertexEvenSymmetricLift_natAdd,
      sixVertexEvenSymmetricLift_castAdd]
    simp
  · have hrev : (Fin.natAdd m j).rev = Fin.castAdd m j.rev := by
      apply Fin.ext
      simp [Fin.rev, Fin.natAdd, Fin.castAdd]
      omega
    rw [hrev, sixVertexEvenSymmetricLift_castAdd,
      sixVertexEvenSymmetricLift_natAdd]
    simp

theorem sixVertexEvenSymmetricLift_injective (m : Nat) :
    Function.Injective (sixVertexEvenSymmetricLift m) := by
  intro q r h
  funext j
  have := congrFun h (Fin.natAdd m j)
  simpa only [sixVertexEvenSymmetricLift_natAdd] using this


def sixVertexEvenSymmetricBetheResidual
    (N m : Nat) (c : Real) (q : Fin m → Real) : Fin m → Real :=
  fun j => sixVertexBetheResidual c N (m + m)
    (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j)



def sixVertexEvenSymmetricBetheResidualGraph (N m : Nat) :
    (Real × (Fin m → Real)) → (Real × (Fin m → Real)) :=
  fun q => (q.1, sixVertexEvenSymmetricBetheResidual N m q.1 q.2)

theorem analyticAt_sixVertexEvenSymmetricBetheResidual_family
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        sixVertexEvenSymmetricBetheResidual N m z.1 z.2) q := by
  let liftPair : (Real × (Fin m → Real)) →L[Real]
      (Real × (Fin (m + m) → Real)) :=
    (ContinuousLinearMap.fst Real Real (Fin m → Real)).prod
      ((sixVertexEvenSymmetricLift m).comp
        (ContinuousLinearMap.snd Real Real (Fin m → Real)))
  let positive : (Fin (m + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (Fin.natAdd m j)
  have hfull : AnalyticAt Real
      (fun z : Real × (Fin (m + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N (m + m) z.2 j)
      (q.1, sixVertexEvenSymmetricLift m q.2) :=
    analyticAt_sixVertexBetheResidual_family N (m + m)
      (q.1, sixVertexEvenSymmetricLift m q.2) hc
  have hlift : AnalyticAt Real (liftPair :
      (Real × (Fin m → Real)) → (Real × (Fin (m + m) → Real))) q :=
    liftPair.analyticAt q
  have hcomp : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z)) q :=
    hfull.comp (f := fun z => liftPair z) (x := q) hlift
  have hpositive := positive.analyticAt
      ((fun z : Real × (Fin (m + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N (m + m) z.2 j)
          (liftPair q))
  have hout : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        positive ((fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z))) q :=
    hpositive.comp
      (f := fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z)) (x := q) hcomp
  have hfun :
      (fun z : Real × (Fin m → Real) =>
        sixVertexEvenSymmetricBetheResidual N m z.1 z.2) =
      (fun z : Real × (Fin m → Real) => fun i =>
        sixVertexBetheResidual z.1 N (m + m)
          (sixVertexEvenSymmetricLift m z.2) (i.addNat m)) := by
    funext z i
    unfold sixVertexEvenSymmetricBetheResidual
    congr 1
    apply Fin.ext
    simp [Fin.natAdd, Fin.addNat]
    omega
  rw [hfun]
  simpa [liftPair, positive, Function.comp_def] using hout

theorem analyticAt_sixVertexEvenSymmetricBetheResidualGraph
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexEvenSymmetricBetheResidualGraph N m) q := by
  exact analyticAt_fst.prod
    (analyticAt_sixVertexEvenSymmetricBetheResidual_family N m q hc)


def sixVertexEvenSymmetricBetheRootJacobian
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    (Fin m → Real) →L[Real] (Fin m → Real) :=
  fderiv Real (sixVertexEvenSymmetricBetheResidual N m c) q

theorem sixVertexBetheResidual_symmetric
    {N n : Nat} {c : Real} {p : Fin n → Real}
    (hp : SixVertexRootSymmetric p) :
    SixVertexRootSymmetric (fun j => sixVertexBetheResidual c N n p j) := by
  intro j
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k)) =
        -(∑ k : Fin n, sixVertexTheta c (p j) (p k)) := by
    calc
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k)) =
          ∑ k : Fin n, sixVertexTheta c (-p j) (-p k.rev) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hp j]
            simp [hp k]
      _ = ∑ k : Fin n, -sixVertexTheta c (p j) (p k.rev) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [sixVertexTheta_neg]
      _ = -(∑ k : Fin n, sixVertexTheta c (p j) (p k)) := by
            rw [Finset.sum_neg_distrib]
            congr 1
            apply Fintype.sum_equiv Fin.revPerm
            intro k
            rfl
  change (N : Real) * p j.rev +
      (∑ k, sixVertexTheta c (p j.rev) (p k)) -
        2 * Real.pi * sixVertexCentralQuantumNumber j.rev =
    -((N : Real) * p j +
      (∑ k, sixVertexTheta c (p j) (p k)) -
        2 * Real.pi * sixVertexCentralQuantumNumber j)
  rw [hsum, hp, sixVertexCentralQuantumNumber_rev]
  ring

theorem sixVertexEvenSymmetricBetheResidual_eq_zero_iff
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexEvenSymmetricBetheResidual N m c q = 0 ↔
      SixVertexSatisfiesBetheEquations c N (m + m)
        (sixVertexEvenSymmetricLift m q) := by
  constructor
  · intro h
    apply (sixVertexBetheResidual_eq_zero_iff c N (m + m)
      (sixVertexEvenSymmetricLift m q)).1
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexEvenSymmetricLift_symmetric m q) (Fin.natAdd m j.rev)
      have hzero : sixVertexBetheResidual c N (m + m)
          (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j.rev) = 0 := by
        simpa [sixVertexEvenSymmetricBetheResidual] using congrFun h j.rev
      have hrev : (Fin.natAdd m j.rev).rev = Fin.castAdd m j := by
        apply Fin.ext
        simp [Fin.rev, Fin.natAdd, Fin.castAdd]
        omega
      rw [hrev] at hsymm
      have hrel : sixVertexBetheResidual c N (m + m)
          (sixVertexEvenSymmetricLift m q) (Fin.castAdd m j) =
          -sixVertexBetheResidual c N (m + m)
            (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j.rev) := by
        simpa only using hsymm
      rw [hrel, hzero, neg_zero]
    · exact congrFun h j
  · intro h
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N (m + m)
      (sixVertexEvenSymmetricLift m q)).2 h (Fin.natAdd m j)


structure SixVertexLocalAnalyticEvenSymmetricBetheBranch
    (N m : Nat) (c : Real) (q : Fin m → Real) where
  roots : Real → (Fin m → Real)
  analyticAt_roots : AnalyticAt Real roots c
  roots_at : roots c = q
  eventually_solution : ∀ᶠ t in nhds c,
    SixVertexSatisfiesBetheEquations t N (m + m)
      (sixVertexEvenSymmetricLift m (roots t))
  eventually_unique : ∀ᶠ z : Real × (Fin m → Real) in nhds (c, q),
    SixVertexSatisfiesBetheEquations z.1 N (m + m)
      (sixVertexEvenSymmetricLift m z.2) → roots z.1 = z.2

theorem sixVertexEvenSymmetricBetheResidualGraph_fderiv_injective
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hjac : Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q)) :
    Function.Injective
      (fderiv Real (sixVertexEvenSymmetricBetheResidualGraph N m) (c, q)) := by
  let H := sixVertexEvenSymmetricBetheResidualGraph N m
  let L := fderiv Real H (c, q)
  let J := sixVertexEvenSymmetricBetheRootJacobian N m c q
  have hH : HasFDerivAt H L (c, q) :=
    (analyticAt_sixVertexEvenSymmetricBetheResidualGraph N m (c, q) hc)
      |>.hasStrictFDerivAt.hasFDerivAt
  let incl : (Fin m → Real) →L[Real] (Real × (Fin m → Real)) :=
    (0 : (Fin m → Real) →L[Real] Real).prod
      (ContinuousLinearMap.id Real (Fin m → Real))
  have hincl : HasFDerivAt (fun r : Fin m → Real => (c, r)) incl q :=
    (hasFDerivAt_const c q).prodMk (hasFDerivAt_id q)
  have hcomp : HasFDerivAt (fun r : Fin m → Real => H (c, r))
      (L.comp incl) q := hH.comp q hincl
  have hres : HasFDerivAt
      (sixVertexEvenSymmetricBetheResidual N m c) J q :=
    (analyticAt_sixVertexEvenSymmetricBetheResidual_family N m (c, q) hc)
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
      simpa [H, sixVertexEvenSymmetricBetheResidualGraph] using
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


theorem exists_sixVertexLocalAnalyticEvenSymmetricBetheBranch
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    (hjac : Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q)) :
    Nonempty (SixVertexLocalAnalyticEvenSymmetricBetheBranch N m c q) := by
  let q₀ : Real × (Fin m → Real) := (c, q)
  let H := sixVertexEvenSymmetricBetheResidualGraph N m
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexEvenSymmetricBetheResidualGraph N m q₀ hc
  have hLinj : Function.Injective L :=
    sixVertexEvenSymmetricBetheResidualGraph_fderiv_injective hc hjac
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
  have hzero : sixVertexEvenSymmetricBetheResidual N m c q = 0 :=
    (sixVertexEvenSymmetricBetheResidual_eq_zero_iff N m c q).2 hsol
  have hHq₀ : H q₀ = (c, (0 : Fin m → Real)) := by
    apply Prod.ext
    · rfl
    · simpa [H, q₀, sixVertexEvenSymmetricBetheResidualGraph] using hzero
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
      SixVertexSatisfiesBetheEquations t N (m + m)
        (sixVertexEvenSymmetricLift m (roots t)) := by
    filter_upwards [hbranchEq] with t ht
    apply (sixVertexEvenSymmetricBetheResidual_eq_zero_iff N m t (roots t)).1
    have hfst := congrArg Prod.fst ht
    have hsnd := congrArg Prod.snd ht
    change (R.symm (t, (0 : Fin m → Real))).1 = t at hfst
    change sixVertexEvenSymmetricBetheResidual N m
      (R.symm (t, (0 : Fin m → Real))).1
      (R.symm (t, (0 : Fin m → Real))).2 = 0 at hsnd
    rw [hfst] at hsnd
    simpa [roots] using hsnd
  have hsource : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      z ∈ R.source := R.open_source.mem_nhds hqsource
  have hunique : ∀ᶠ z : Real × (Fin m → Real) in nhds q₀,
      SixVertexSatisfiesBetheEquations z.1 N (m + m)
        (sixVertexEvenSymmetricLift m z.2) → roots z.1 = z.2 := by
    filter_upwards [hsource] with z hz hzsol
    have hzres : sixVertexEvenSymmetricBetheResidual N m z.1 z.2 = 0 :=
      (sixVertexEvenSymmetricBetheResidual_eq_zero_iff N m z.1 z.2).2 hzsol
    have hHz : H z = (z.1, (0 : Fin m → Real)) := by
      apply Prod.ext
      · rfl
      · simpa [H, sixVertexEvenSymmetricBetheResidualGraph] using hzres
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
