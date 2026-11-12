/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumFactor





open MeasureTheory Set

namespace StatMech.FK



def IsErgodicFor {G Omega : Type*} [MeasurableSpace Omega]
    (shift : G -> Omega -> Omega) (mu : Measure Omega) : Prop :=
  (∀ g, MeasurePreserving (shift g) mu mu) ∧
    ∀ s : Set Omega, MeasurableSet s ->
      (∀ g, shift g ⁻¹' s = s) ->
        mu s = 0 ∨ mu s = mu Set.univ


theorem IsErgodicFor.map
    {G Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    {sourceShift : G -> Omega -> Omega} {targetShift : G -> Xi -> Xi}
    {mu : Measure Omega} (hergodic : IsErgodicFor sourceShift mu)
    (factor : Omega -> Xi) (hfactor : Measurable factor)
    (htarget : ∀ g, Measurable (targetShift g))
    (hequivariant : ∀ g omega,
      factor (sourceShift g omega) = targetShift g (factor omega)) :
    IsErgodicFor targetShift (Measure.map factor mu) := by
  refine ⟨?_, ?_⟩
  · intro g
    refine ⟨htarget g, ?_⟩
    rw [Measure.map_map (htarget g) hfactor]
    have hcomp : targetShift g ∘ factor = factor ∘ sourceShift g := by
      funext omega
      exact (hequivariant g omega).symm
    rw [hcomp, ← Measure.map_map hfactor (hergodic.1 g).measurable,
      (hergodic.1 g).map_eq]
  · intro s hs hinvariant
    have hpre : MeasurableSet (factor ⁻¹' s) := hs.preimage hfactor
    have hpreInvariant : ∀ g, sourceShift g ⁻¹' (factor ⁻¹' s) =
        factor ⁻¹' s := by
      intro g
      ext omega
      simp only [Set.mem_preimage]
      rw [hequivariant g omega]
      exact Set.ext_iff.mp (hinvariant g) (factor omega)
    rcases hergodic.2 (factor ⁻¹' s) hpre hpreInvariant with hzero | hfull
    · left
      rw [Measure.map_apply hfactor hs, hzero]
    · right
      rw [Measure.map_apply hfactor hs,
        Measure.map_apply hfactor MeasurableSet.univ,
        Set.preimage_univ, hfull]


abbrev pottsSpinShift {d q : Nat} (g : Multiplicative (Lattice.Site d))
    (spin : Lattice.Site d -> Fin q) : Lattice.Site d -> Fin q :=
  pottsLabelShift g spin



theorem pottsJoint_fst_equivariant {d q : Nat}
    (g : Multiplicative (Lattice.Site d))
    (joint : (Lattice.Site d -> Fin q) ×
      ConfigSpace (Sym2 (Lattice.Site d))) :
    (pottsJointShift g joint).1 = pottsSpinShift g joint.1 := rfl



theorem pottsClusterSumJointMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    (hsource : IsErgodicFor pottsClusterFactorInputShift
      (edgeMeasure.prod (pottsIIDLabelMeasure d q))) :
    IsErgodicFor pottsJointShift
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
  exact hsource.map (pottsClusterSumJointFactor boundaryColor)
    (measurable_pottsClusterSumJointFactor boundaryColor)
    (fun g =>
      ((measurable_pi_lambda _ fun x =>
        measurable_pi_apply (g⁻¹ • x)).comp measurable_fst).prodMk
        ((ConfigSpace.measurable_shift g).comp measurable_snd))
    (pottsClusterSumJointFactor_shift boundaryColor)


theorem pottsClusterSumSpinMarginal_isErgodicFor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    (hjoint : IsErgodicFor pottsJointShift
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) :
    IsErgodicFor pottsSpinShift
      (Measure.map Prod.fst
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure)) := by
  exact hjoint.map Prod.fst measurable_fst
    (fun _ => measurable_pi_lambda _ fun x => measurable_pi_apply _)
    (fun _ _ => rfl)

end StatMech.FK
