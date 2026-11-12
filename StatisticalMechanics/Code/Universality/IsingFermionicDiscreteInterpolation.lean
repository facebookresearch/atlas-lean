/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCaratheodoryApproximation
import Mathlib.Topology.UniformSpace.Ascoli











open Filter Metric Set Topology
open scoped UniformConvergence

noncomputable section

namespace StatMech.FrontierA



theorem equicontinuousFamily_restrictionClosure_compact
    {ι : Type*} (F : ι → Complex → Complex)
    (K : Set Complex) (hK : IsCompact K)
    (heq : EquicontinuousOn F K)
    (hbounded : ∃ C : Real, ∀ i z, z ∈ K → ‖F i z‖ ≤ C) :
    IsCompact (closure (Set.range (fun i =>
      UniformFun.ofFun (fun z : K => F i z)))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ι → K →ᵤ Complex := fun i => UniformFun.ofFun (fun z => F i z)
  let S : Set (K →ᵤ Complex) := Set.range f
  let sets : Set (Set K) := {Set.univ}
  let eval : (K →ᵤ Complex) → K → Complex := UniformFun.toFun
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun sets ∘ eval) := by
    let e := UniformOnFun.uniformEquivUniformFun Complex sets
      (show Set.univ ∈ sets by simp [sets])
    change IsClosedEmbedding e.symm
    exact e.symm.toHomeomorph.isClosedEmbedding
  have hSEq : EquicontinuousOn (eval ∘ ((↑) : S → K →ᵤ Complex)) Set.univ := by
    rw [equicontinuousOn_univ]
    have hrestrict : Equicontinuous (K.restrict ∘ F) :=
      (equicontinuous_restrict_iff F).2 heq
    let pick : S → ι := fun q => Classical.choose q.property
    have hpick (q : S) : f (pick q) = q := Classical.choose_spec q.property
    have hsub := hrestrict.comp pick
    convert hsub using 1
    funext q z
    have h := congrArg (fun a : K →ᵤ Complex => UniformFun.toFun a z) (hpick q)
    simpa only [f, eval, Function.comp_apply] using h.symm
  obtain ⟨C, hC⟩ := hbounded
  have hpoint : ∀ T ∈ sets, ∀ z ∈ T,
      ∃ Q : Set Complex, IsCompact Q ∧ ∀ q ∈ S, eval q z ∈ Q := by
    intro T hT z _hz
    have hTuniv : T = Set.univ := by
      simpa only [sets, Set.mem_singleton_iff] using hT
    subst T
    refine ⟨closedBall 0 (max C 0), isCompact_closedBall 0 (max C 0), ?_⟩
    intro q hq
    obtain ⟨i, rfl⟩ := hq
    rw [mem_closedBall]
    simpa only [eval, f, dist_zero_right] using
      (hC i z z.property).trans (le_max_left C 0)
  have hcompact : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := sets)
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact isCompact_univ)
      hclosed
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact hSEq)
      hpoint
  simpa only [S, f] using hcompact



theorem equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    (F : Nat → Complex → Complex) (U : Set Complex) (hU : IsOpen U)
    (heq : ∀ K : Set Complex, IsCompact K → K ⊆ U → EquicontinuousOn F K)
    (hbounded : ∀ K : Set Complex, IsCompact K → K ⊆ U →
      ∃ C : Real, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (E : CompactExhaustion U) :
    IsLocallyUniformlySequentiallyPrecompact F U := by
  classical
  intro phi hphi
  let X : Nat → Type := fun n => E.sets n →ᵤ Complex
  let S : ∀ n, Set (X n) := fun n => closure (Set.range (fun k =>
    UniformFun.ofFun (fun z : E.sets n => F (phi k) z)))
  have hS : ∀ n, IsCompact (S n) := by
    intro n
    apply equicontinuousFamily_restrictionClosure_compact
    · exact E.isCompact n
    · exact (heq (E.sets n) (E.isCompact n) (E.subset n)).comp phi
    · obtain ⟨C, hC⟩ := hbounded (E.sets n) (E.isCompact n) (E.subset n)
      exact ⟨C, fun k => hC (phi k)⟩
  let P : Set (∀ n, X n) := Set.univ.pi S
  have hP : IsCompact P := by
    simpa only [P] using isCompact_univ_pi hS
  let x : Nat → ∀ n, X n := fun k n =>
    UniformFun.ofFun (fun z : E.sets n => F (phi k) z)
  have hx : ∀ k, x k ∈ P := by
    intro k n _hn
    exact subset_closure ⟨k, rfl⟩
  obtain ⟨a, ha, psi, hpsi, hlim⟩ := hP.tendsto_subseq hx
  have hcoord : ∀ n, TendstoUniformly
      (fun k (z : E.sets n) => F (phi (psi k)) z)
      (fun z => a n z) atTop := by
    intro n
    have hn : Tendsto (fun k => x (psi k) n) atTop (nhds (a n)) :=
      (tendsto_pi_nhds.mp hlim) n
    have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hn
    simpa only [x, Function.comp_apply] using hu
  let pick : ∀ z : Complex, z ∈ U → Nat := fun z hz =>
    Classical.choose (E.cofinal {z} isCompact_singleton (by simpa using hz))
  have hpick : ∀ (z : Complex) (hz : z ∈ U), z ∈ E.sets (pick z hz) := by
    intro z hz
    exact Classical.choose_spec
      (E.cofinal {z} isCompact_singleton (by simpa using hz)) (by simp)
  let g : Complex → Complex := fun z => if hz : z ∈ U then
    a (pick z hz) ⟨z, hpick z hz⟩ else 0
  have hg_coord : ∀ n z (hz : z ∈ E.sets n), g z = a n ⟨z, hz⟩ := by
    intro n z hz
    have hzU : z ∈ U := E.subset n hz
    simp only [g, dif_pos hzU]
    have hp := (hcoord (pick z hzU)).tendsto_at ⟨z, hpick z hzU⟩
    have hn := (hcoord n).tendsto_at ⟨z, hz⟩
    apply tendsto_nhds_unique
      (show Tendsto (fun k => F (phi (psi k)) z) atTop
        (nhds (a (pick z hzU) ⟨z, hpick z hzU⟩)) by simpa using hp)
    exact (show Tendsto (fun k => F (phi (psi k)) z) atTop
      (nhds (a n ⟨z, hz⟩)) by simpa using hn)
  refine ⟨psi, hpsi, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨n, hKn⟩ := E.cofinal K hK hKU
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent := (Metric.tendstoUniformly_iff.mp (hcoord n)) epsilon hepsilon
  filter_upwards [hevent] with k hk
  intro z hz
  rw [hg_coord n z (hKn hz)]
  exact hk ⟨z, hKn hz⟩

end StatMech.FrontierA

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)




structure StableDiscreteInterpolation where
  interpolant : Nat → Complex → Complex
  continuousOn : ∀ n, ContinuousOn (interpolant n) A.U
  medial : ∀ n e, interpolant n (A.medialEmbedding n e) =
    @FKIsingDobrushinDomain.normalizedFermionicObservable
      (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e
  compactEquicontinuous : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    EquicontinuousOn interpolant K

variable (I : A.StableDiscreteInterpolation)



theorem stableInterpolant_compact_eventually_near_literalObservable
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ∃ e : A.M n,
      dist z (A.medialEmbedding n e) ≤ A.mesh n ∧
      I.interpolant n (A.medialEmbedding n e) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e := by
  filter_upwards [A.compact_eventually_near_medial K hK hKU] with n hn
  intro z hz
  obtain ⟨e, he⟩ := hn z hz
  exact ⟨e, he, I.medial n e⟩




def StableDiscreteInterpolation.HasCompactLocalBounds : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ C : Real, ∀ n z, z ∈ K → ‖I.interpolant n z‖ ≤ C



theorem StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds) :
    StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact
      I.interpolant A.U :=
  StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    I.interpolant A.U A.isOpen I.compactEquicontinuous hbounded E



def StableDiscreteInterpolation.SubsequentialMoreraPrimitive
    (target Phi : Complex → Complex) : Prop :=
  ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
    StrictMono phi → StrictMono psi →
    TendstoLocallyUniformlyOn
      (fun n => I.interpolant (phi (psi n))) f atTop A.U →
    Complex.IsConservativeOn f A.U ∧
    ∃ (P : Complex → Complex) (C : Real),
      DifferentiableOn Complex P A.U ∧
      Set.EqOn (deriv P) (fun z => f z ^ 2) A.U ∧
      (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
      f A.root = target A.root





theorem StableDiscreteInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds)
    (hidentify : StableDiscreteInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  apply StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    I.interpolant target A.U A.isOpen
    (StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact
      A I E hbounded)
  intro phi psi f hphi hpsi hlimit
  obtain ⟨hMorera, P, C, hP, hPderiv, him, hanchor⟩ :=
    hidentify phi psi f hphi hpsi hlimit
  have hfContinuous : ContinuousOn f A.U :=
    hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => I.continuousOn (phi (psi n))))
  have hf : DifferentiableOn Complex f A.U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      A.isOpen).1 ⟨hMorera, hfContinuous⟩
  have hsquare := isingFermionic_square_eq_of_primitive_im_eq
    f target P Phi A.U A.root C A.isOpen A.isPreconnected A.root_mem
      hP hPhi hPderiv hPhideriv him
  exact isingFermionic_squareRoot_unique_of_anchor
    f target A.U A.root A.isOpen A.isPreconnected A.root_mem hf htarget
      hsquare hanchor htarget_ne




theorem StableDiscreteInterpolation.literalObservable_tendsto_on_compacts
    (target : Complex → Complex)
    (hlimit : TendstoLocallyUniformlyOn I.interpolant target atTop A.U)
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ e : A.M n, A.medialEmbedding n e ∈ K →
      dist
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
        (target (A.medialEmbedding n e)) < epsilon := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact A.isOpen] at hlimit
  have hKlimit := hlimit K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hKlimit
  filter_upwards [hKlimit epsilon hepsilon] with n hn
  intro e he
  rw [← I.medial n e]
  simpa only [dist_comm] using hn (A.medialEmbedding n e) he

end FKIsingCaratheodoryApproximation

end StatMech.Universality

end
