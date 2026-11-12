/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.CurrentSelectionIndependence
import Code.FrontierB.CurrentMixingErgodicity
import Code.FrontierB.FreeEvenHomogeneity

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Ising Lattice Sharpness



def currentShiftFinset {E H : Type*} [Group H] [MulAction H E]
    [DecidableEq E] (g : H) (S : Finset E) : Finset E :=
  S.image fun e => g⁻¹ • e



noncomputable def currentShiftFinsetEquiv
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) : ↑(currentShiftFinset g S) ≃ ↑S where
  toFun e := ⟨g • e.1, by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp e.2
    rw [← hxe, smul_inv_smul]
    exact hx⟩
  invFun e := ⟨g⁻¹ • e.1, Finset.mem_image_of_mem _ e.2⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

@[simp] theorem currentShiftFinsetEquiv_val
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (e : ↑(currentShiftFinset g S)) :
    (currentShiftFinsetEquiv g S e).1 = g • e.1 := rfl

@[simp] theorem currentShiftFinsetEquiv_symm_val
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (e : ↑S) :
    ((currentShiftFinsetEquiv g S).symm e).1 = g⁻¹ • e.1 := rfl


noncomputable def currentShiftPattern {E H X : Type*} [Group H] [MulAction H E]
    [DecidableEq E] (g : H) (S : Finset E) (a : ↑S -> X) :
    ↑(currentShiftFinset g S) -> X :=
  fun e => a (currentShiftFinsetEquiv g S e)

theorem currentLocalParity_shiftPattern
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (a : ↑S -> Nat) :
    currentLocalParity (currentShiftPattern g S a) =
      currentShiftPattern g S (currentLocalParity a) := by
  rfl



theorem preimage_currentCylinder_singleton_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (a : ↑S -> Nat) :
    (currentShift g) ⁻¹' currentCylinder S {a} =
      currentCylinder (currentShiftFinset g S)
        {currentShiftPattern g S a} := by
  ext m
  simp only [Set.mem_preimage, currentCylinder, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro h
    funext e
    have he := congrFun h (currentShiftFinsetEquiv g S e)
    simpa [restrictCurrent, currentShift, currentShiftPattern] using he
  · intro h
    funext e
    have he := congrFun h ((currentShiftFinsetEquiv g S).symm e)
    simpa [restrictCurrent, currentShift, currentShiftPattern] using he


theorem currentShiftFinset_lattice
    (d : Nat) (g : Multiplicative (Site d))
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (↑(currentShiftFinset g S) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  have hfedge := hS hf
  induction f using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at hfedge
      rw [Percolation.smul_sym2_mk, SimpleGraph.mem_edgeSet]
      exact (Percolation.hyper_adj_smul g⁻¹ x y).2 hfedge



theorem preimage_currentParityAvoidCylinder_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (F : Finset E) :
    (currentShift g) ⁻¹' currentParityAvoidCylinder F =
      currentParityAvoidCylinder (currentShiftFinset g F) := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder]
  constructor
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact h f hf
  · intro h e he
    have hs : g⁻¹ • e ∈ currentShiftFinset g F :=
      Finset.mem_image_of_mem _ he
    exact h (g⁻¹ • e) hs


theorem edgeSpinSum_shift
    (d : Nat) (g : Multiplicative (Site d))
    (F : Finset (Sym2 (Site d))) (omega : ConfigSpace (Site d)) :
    edgeSpinSum F (ConfigSpace.shift g omega) =
      edgeSpinSum (currentShiftFinset g F) omega := by
  unfold edgeSpinSum currentShiftFinset
  rw [Finset.sum_image (fun a _ b _ hab => MulAction.injective g⁻¹ hab)]
  apply Finset.sum_congr rfl
  intro e he
  simpa using iptp_bond_shift g omega (g⁻¹ • e)



theorem integral_exp_neg_edgeSpinSum_shift
    (d : Nat) (beta : Real)
    (mu : Measure (ConfigSpace (Site d)))
    (hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu)
    (g : Multiplicative (Site d)) (F : Finset (Sym2 (Site d))) :
    (∫ omega, Real.exp (-beta * edgeSpinSum
        (currentShiftFinset g F) omega) ∂mu) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu := by
  let e : ConfigSpace (Site d) ≃ᵐ ConfigSpace (Site d) :=
    { toEquiv :=
        { toFun := ConfigSpace.shift g
          invFun := ConfigSpace.shift g⁻¹
          left_inv := fun omega => by
            exact congrFun (ConfigSpace.shift_inv_comp g) omega
          right_inv := fun omega => by
            exact congrFun (ConfigSpace.shift_comp_inv g) omega }
      measurable_toFun := ConfigSpace.measurable_shift g
      measurable_invFun := ConfigSpace.measurable_shift g⁻¹ }
  have hmp : MeasurePreserving e mu mu := hti g
  have hint := hmp.integral_comp'
    (fun omega => Real.exp (-beta * edgeSpinSum F omega))
  change (∫ omega, Real.exp (-beta * edgeSpinSum F
      (ConfigSpace.shift g omega)) ∂mu) =
    ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu at hint
  simpa only [edgeSpinSum_shift] using hint



theorem infinitePlusCurrentMeasure_parityAvoid_eq
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  have hcurrent := (plusBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal
    F {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hcurrent
  exact tendsto_nhds_unique hcurrent
    (plusBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta.le F hF)



theorem infiniteFreeCurrentMeasure_parityAvoid_eq
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  have hcurrent := (freeBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal
    F {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hcurrent
  exact tendsto_nhds_unique hcurrent
    (freeBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta.le F hF)



theorem finiteParityPMF_shiftPattern
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (beta : Real) (hbeta : 0 < beta)
    (odd : ↑S -> Bool) (a : ↑S -> Nat) :
    finiteParityPMF (currentShiftFinset g S) beta hbeta
        (currentShiftPattern g S odd) (currentShiftPattern g S a) =
      finiteParityPMF S beta hbeta odd a := by
  rw [finiteParityPMF_apply, finiteParityPMF_apply]
  congr 1
  unfold finiteParityKernel currentShiftPattern
  apply Fintype.prod_equiv (currentShiftFinsetEquiv g S)
  intro e
  rfl


theorem preimage_currentParityPatternCylinder_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (odd : ↑S -> Bool) :
    (currentShift g) ⁻¹' currentParityPatternCylinder S odd =
      currentParityPatternCylinder (currentShiftFinset g S)
        (currentShiftPattern g S odd) := by
  ext m
  simp only [Set.mem_preimage, currentParityPatternCylinder]
  constructor
  · intro h
    funext e
    have he := congrFun h (currentShiftFinsetEquiv g S e)
    simpa [currentLocalParity, restrictCurrent, currentShift,
      currentShiftPattern] using he
  · intro h
    funext e
    have he := congrFun h ((currentShiftFinsetEquiv g S).symm e)
    simpa [currentLocalParity, restrictCurrent, currentShift,
      currentShiftPattern] using he


noncomputable def currentShiftLaw {E H : Type*} [Countable E]
    [Group H] [MulAction H E] (g : H)
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    ProbabilityMeasure (InfiniteCurrentConfig E) :=
  mu.map (continuous_currentShift g).measurable.aemeasurable

theorem currentShiftLaw_apply {E H : Type*} [Countable E]
    [Group H] [MulAction H E] (g : H)
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (A : Set (InfiniteCurrentConfig E)) (hA : MeasurableSet A) :
    (currentShiftLaw g mu : Measure (InfiniteCurrentConfig E)) A =
      (mu : Measure (InfiniteCurrentConfig E)) ((currentShift g) ⁻¹' A) := by
  exact Measure.map_apply (measurable_currentShift g) hA



theorem currentParityMarginalPMF_currentShiftLaw_eq
    (d : Nat) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (g : Multiplicative (Site d))
    (havoid : ∀ F : Finset (Sym2 (Site d)),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      (mu : Measure _) ((currentShift g) ⁻¹'
          currentParityAvoidCylinder F) =
        (mu : Measure _) (currentParityAvoidCylinder F))
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    currentParityMarginalPMF (currentShiftLaw g mu) S =
      currentParityMarginalPMF mu S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  rw [currentShiftLaw_apply]
  · exact havoid (ambientSubfinset S T)
      (ambientSubfinset_lattice d S hS T)
  · have hset := currentParityAvoidCylinder_eq_currentCylinder
      (ambientSubfinset S T)
    rw [hset]
    exact measurableSet_currentCylinder _ _




theorem currentLimit_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} = 1)
    (hfactor : ∀ (S : Finset (Sym2 (Site d))),
      (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      ∀ a : ↑S -> Nat,
        (mu : Measure _) (currentCylinder S {a}) =
          (mu : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) *
            finiteParityPMF S beta hbeta (currentLocalParity a) a)
    (havoid : ∀ (g : Multiplicative (Site d))
      (F : Finset (Sym2 (Site d))),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      (mu : Measure _) ((currentShift g) ⁻¹'
          currentParityAvoidCylinder F) =
        (mu : Measure _) (currentParityAvoidCylinder F)) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  intro g
  let rho := currentShiftLaw g mu
  have hrhoZero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (rho : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} = 1 := by
    intro e he
    rw [currentShiftLaw_apply]
    · have hpre : (currentShift g) ⁻¹'
          {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} =
          {m : InfiniteCurrentConfig (Sym2 (Site d)) |
            m (g⁻¹ • e) = 0} := rfl
      rw [hpre]
      apply hzero
      intro hedge
      apply he
      induction e using Sym2.inductionOn with
      | _ x y =>
          rw [Percolation.smul_sym2_mk] at hedge
          rw [SimpleGraph.mem_edgeSet] at hedge ⊢
          exact (Percolation.hyper_adj_smul g⁻¹ x y).1 hedge
    · exact (measurable_pi_apply e) (MeasurableSet.singleton 0)
  have hparity (S : Finset (Sym2 (Site d)))
      (hS : (↑S : Set (Sym2 (Site d))) ⊆
        (hypercubicLattice d).edgeSet) :
      currentParityMarginalPMF rho S = currentParityMarginalPMF mu S :=
    currentParityMarginalPMF_currentShiftLaw_eq d mu g (havoid g) S hS
  have hlatticeMarginal (S : Finset (Sym2 (Site d)))
      (hS : (↑S : Set (Sym2 (Site d))) ⊆
        (hypercubicLattice d).edgeSet) :
      currentMarginal rho S = currentMarginal mu S := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    rw [currentMarginal_apply, currentMarginal_apply]
    rw [currentShiftLaw_apply]
    · rw [preimage_currentCylinder_singleton_currentShift]
      let Sg := currentShiftFinset g S
      let ag := currentShiftPattern g S a
      have hSg : (↑Sg : Set (Sym2 (Site d))) ⊆
          (hypercubicLattice d).edgeSet :=
        currentShiftFinset_lattice d g S hS
      rw [hfactor Sg hSg ag, hfactor S hS a]
      have hparEvent :
          (mu : Measure _)
              (currentParityPatternCylinder Sg (currentLocalParity ag)) =
            (rho : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) := by
        rw [currentShiftLaw_apply]
        · rw [preimage_currentParityPatternCylinder_currentShift,
            currentLocalParity_shiftPattern]
        · have hset : currentParityPatternCylinder S (currentLocalParity a) =
              currentCylinder S
                {b | currentLocalParity b = currentLocalParity a} := rfl
          rw [hset]
          exact measurableSet_currentCylinder _ _
      rw [hparEvent]
      have hp := congrArg
        (fun p : PMF (↑S -> Bool) => p (currentLocalParity a))
        (hparity S hS)
      have hp' :
          (rho : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) =
            (mu : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) := by
        simpa only [currentParityMarginalPMF_apply] using hp
      rw [hp']
      have hk : finiteParityPMF Sg beta hbeta
            (currentLocalParity ag) ag =
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
        simpa [Sg, ag, currentLocalParity_shiftPattern] using
          (finiteParityPMF_shiftPattern g S beta hbeta
            (currentLocalParity a) a)
      rw [hk]
    · exact measurableSet_currentCylinder _ _
  have hmarginal : ∀ S : Finset (Sym2 (Site d)),
      currentMarginal rho S = currentMarginal mu S := by
    intro S
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    rw [currentMarginal_apply, currentMarginal_apply,
      currentCylinder_singleton_reduce_lattice d rho S hrhoZero a,
      currentCylinder_singleton_reduce_lattice d mu S hzero a]
    split_ifs
    · have hL := hlatticeMarginal (latticeEdgePart d S)
        (latticeEdgePart_lattice d S)
      have happ := congrArg (fun p : ProbabilityMeasure
        (↑(latticeEdgePart d S) -> Nat) =>
          (p : Measure (↑(latticeEdgePart d S) -> Nat))
            {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => Nat)
              (latticeEdgePart_subset d S) a}) hL
      simpa only [currentMarginal_apply] using happ
    · rfl
  have hrho : rho = mu := ProbabilityMeasure.ext_of_currentMarginal_eq hmarginal
  refine ⟨measurable_currentShift g, ?_⟩
  exact congrArg ProbabilityMeasure.toMeasure hrho



theorem infinitePlusCurrentMeasure_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  apply currentLimit_isTranslationInvariant d beta hbeta
    (infinitePlusCurrentMeasure d beta hbeta.le)
  · intro e he
    exact plusCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
  · intro S hS a
    exact plusCurrentLimit_pattern_factor d beta hbeta S hS
      (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le) a
  · intro g F hF
    rw [preimage_currentParityAvoidCylinder_currentShift,
      infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta
        (currentShiftFinset g F) (currentShiftFinset_lattice d g F hF),
      infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta F hF]
    rw [integral_exp_neg_edgeSpinSum_shift d beta
      (plusState d beta 0 : Measure (ConfigSpace (Site d)))
      (iptp_plusState_isTranslationInvariant hbeta.le le_rfl) g F]
    rw [show (currentShiftFinset g F).card = F.card by
      unfold currentShiftFinset
      exact Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]



theorem infiniteFreeCurrentMeasure_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  apply currentLimit_isTranslationInvariant d beta hbeta
    (infiniteFreeCurrentMeasure d beta hbeta.le)
  · intro e he
    exact freeCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
  · intro S hS a
    exact freeCurrentLimit_pattern_factor d beta hbeta S hS
      (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le) a
  · intro g F hF
    rw [preimage_currentParityAvoidCylinder_currentShift,
      infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta
        (currentShiftFinset g F) (currentShiftFinset_lattice d g F hF),
      infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta F hF]
    rw [integral_exp_neg_edgeSpinSum_shift d beta
      (freeState d beta 0 : Measure (ConfigSpace (Site d)))
      (freeState_isTranslationInvariant d beta hbeta.le) g F]
    rw [show (currentShiftFinset g F).card = F.card by
      unfold currentShiftFinset
      exact Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]

end StatMech.FrontierB
