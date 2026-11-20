/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair











namespace StatMech.FrontierD

noncomputable section



structure SixVertexDirectedSimpleArc (T : EvenTorus) where
  length : Nat
  length_pos : 0 < length
  edge : Fin length → SixVertexDirectedTorusEdge T
  head_eq_next_tail : ∀ i : Fin (length - 1),
    (edge ⟨i.val, by omega⟩).head =
      (edge ⟨i.val + 1, by omega⟩).tail
  tail_injective : Function.Injective (fun i => (edge i).tail)
  physical_injective : Function.Injective (fun i => (edge i).physical)

def SixVertexDirectedSimpleArc.firstIndex {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : Fin arc.length :=
  ⟨0, arc.length_pos⟩

def SixVertexDirectedSimpleArc.lastIndex {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : Fin arc.length :=
  ⟨arc.length - 1, by
    have := arc.length_pos
    omega⟩

def SixVertexDirectedSimpleArc.start {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : T.Vertex :=
  (arc.edge arc.firstIndex).tail

def SixVertexDirectedSimpleArc.finish {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : T.Vertex :=
  (arc.edge arc.lastIndex).head



structure SixVertexDirectedComplementaryArcPair (T : EvenTorus) where
  first : SixVertexDirectedSimpleArc T
  second : SixVertexDirectedSimpleArc T
  first_finish_eq_second_start : first.finish = second.start
  second_finish_eq_first_start : second.finish = first.start
  tail_disjoint : ∀ i j, (first.edge i).tail ≠ (second.edge j).tail
  physical_disjoint : ∀ i j,
    (first.edge i).physical ≠ (second.edge j).physical


def sixVertexFinPrefixIndex {N : Nat} (cut : Fin N) (i : Fin cut.val) : Fin N :=
  ⟨i.val, lt_trans i.isLt cut.isLt⟩


def sixVertexFinSuffixIndex {N : Nat} (cut : Fin N)
    (i : Fin (N - cut.val)) : Fin N :=
  ⟨cut.val + i.val, by omega⟩

@[simp] theorem sixVertexFinPrefixIndex_val {N : Nat} (cut : Fin N)
    (i : Fin cut.val) : (sixVertexFinPrefixIndex cut i).val = i.val := rfl

@[simp] theorem sixVertexFinSuffixIndex_val {N : Nat} (cut : Fin N)
    (i : Fin (N - cut.val)) :
    (sixVertexFinSuffixIndex cut i).val = cut.val + i.val := rfl

theorem sixVertexFinPrefixIndex_injective {N : Nat} (cut : Fin N) :
    Function.Injective (sixVertexFinPrefixIndex cut) := by
  intro i j h
  apply Fin.ext
  have hval : (sixVertexFinPrefixIndex cut i).val =
      (sixVertexFinPrefixIndex cut j).val := congrArg Fin.val h
  exact hval

theorem sixVertexFinSuffixIndex_injective {N : Nat} (cut : Fin N) :
    Function.Injective (sixVertexFinSuffixIndex cut) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [sixVertexFinSuffixIndex_val] at hval
  omega

theorem sixVertexFinPrefixIndex_ne_suffixIndex {N : Nat} (cut : Fin N)
    (i : Fin cut.val) (j : Fin (N - cut.val)) :
    sixVertexFinPrefixIndex cut i ≠ sixVertexFinSuffixIndex cut j := by
  intro h
  have hval := congrArg Fin.val h
  simp only [sixVertexFinPrefixIndex_val, sixVertexFinSuffixIndex_val] at hval
  omega

private theorem finitePeriodicSucc_prefixIndex
    {N : Nat} (hN : 0 < N) (cut : Fin N) (i : Nat)
    (hi : i + 1 < cut.val) :
    finitePeriodicSucc hN (sixVertexFinPrefixIndex cut ⟨i, by omega⟩) =
      sixVertexFinPrefixIndex cut ⟨i + 1, hi⟩ := by
  apply Fin.ext
  change (i + 1) % N = i + 1
  rw [Nat.mod_eq_of_lt]
  omega

private theorem finitePeriodicSucc_suffixIndex
    {N : Nat} (hN : 0 < N) (cut : Fin N) (i : Nat)
    (hi : i + 1 < N - cut.val) :
    finitePeriodicSucc hN (sixVertexFinSuffixIndex cut ⟨i, by omega⟩) =
      sixVertexFinSuffixIndex cut ⟨i + 1, hi⟩ := by
  apply Fin.ext
  change (cut.val + i + 1) % N = cut.val + (i + 1)
  rw [Nat.mod_eq_of_lt]
  · omega
  · have := cut.isLt
    omega


def sixVertexDegreeTwoStrandCycleForwardArc
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)))
    (hcut : 0 < cut.val) : SixVertexDirectedSimpleArc T := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  refine {
    length := cut.val
    length_pos := hcut
    edge := fun i => cycle.edge (sixVertexFinPrefixIndex cut i)
    head_eq_next_tail := ?_
    tail_injective := ?_
    physical_injective := ?_ }
  · intro i
    have hnext := cycle.head_eq_next_tail
      (sixVertexFinPrefixIndex cut ⟨i.val, by omega⟩)
    rw [finitePeriodicSucc_prefixIndex cycle.length_pos cut i.val (by omega)] at hnext
    exact hnext
  · intro i j h
    apply sixVertexFinPrefixIndex_injective cut
    exact cycle.tail_injective h
  · intro i j h
    apply sixVertexFinPrefixIndex_injective cut
    exact cycle.physical_injective h


def sixVertexDegreeTwoStrandCycleBackwardArc
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) : SixVertexDirectedSimpleArc T := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  refine {
    length := orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed) - cut.val
    length_pos := by
      omega
    edge := fun i => cycle.edge (sixVertexFinSuffixIndex cut i)
    head_eq_next_tail := ?_
    tail_injective := ?_
    physical_injective := ?_ }
  · intro i
    have hnext := cycle.head_eq_next_tail
      (sixVertexFinSuffixIndex cut ⟨i.val, by
        change i.val < orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val
        omega⟩)
    rw [finitePeriodicSucc_suffixIndex cycle.length_pos cut i.val (by
      change i.val + 1 < orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed) - cut.val
      omega)] at hnext
    exact hnext
  · intro i j h
    apply sixVertexFinSuffixIndex_injective cut
    exact cycle.tail_injective h
  · intro i j h
    apply sixVertexFinSuffixIndex_injective cut
    exact cycle.physical_injective h

theorem sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) (hcut : 0 < cut.val) :
    (sixVertexDegreeTwoStrandCycleForwardArc
      homega heta hdegree seed cut hcut).finish =
      (sixVertexDegreeTwoStrandCycleBackwardArc
        homega heta hdegree seed cut).start := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  have hcutLtCycle : cut.val < cycle.length := by
    change cut.val < orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)
    exact cut.isLt
  change (cycle.edge (sixVertexFinPrefixIndex cut
      ⟨cut.val - 1, by omega⟩)).head =
    (cycle.edge (sixVertexFinSuffixIndex cut ⟨0, by
      omega⟩)).tail
  have hnext := cycle.head_eq_next_tail
    (sixVertexFinPrefixIndex cut ⟨cut.val - 1, by omega⟩)
  rw [show finitePeriodicSucc cycle.length_pos
      (sixVertexFinPrefixIndex cut ⟨cut.val - 1, by omega⟩) =
        sixVertexFinSuffixIndex cut ⟨0, by
          change 0 < orderOf (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed) - cut.val
          omega⟩ by
      apply Fin.ext
      change (cut.val - 1 + 1) %
        orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) = cut.val + 0
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega] at hnext
  exact hnext

theorem sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) (hcut : 0 < cut.val) :
    (sixVertexDegreeTwoStrandCycleBackwardArc
      homega heta hdegree seed cut).finish =
      (sixVertexDegreeTwoStrandCycleForwardArc
        homega heta hdegree seed cut hcut).start := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  change (cycle.edge (sixVertexFinSuffixIndex cut
      ⟨cycle.length - cut.val - 1, by
        change orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val - 1 <
            orderOf (sixVertexDegreeTwoStrandCyclePerm
              homega heta hdegree seed) - cut.val
        omega⟩)).head =
    (cycle.edge (sixVertexFinPrefixIndex cut ⟨0, hcut⟩)).tail
  have hnext := cycle.head_eq_next_tail
    (sixVertexFinSuffixIndex cut
      ⟨cycle.length - cut.val - 1, by
        change orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val - 1 <
            orderOf (sixVertexDegreeTwoStrandCyclePerm
              homega heta hdegree seed) - cut.val
        omega⟩)
  rw [show finitePeriodicSucc cycle.length_pos
      (sixVertexFinSuffixIndex cut
        ⟨cycle.length - cut.val - 1, by
          change orderOf (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed) - cut.val - 1 <
              orderOf (sixVertexDegreeTwoStrandCyclePerm
                homega heta hdegree seed) - cut.val
          omega⟩) =
        sixVertexFinPrefixIndex cut ⟨0, hcut⟩ by
      apply Fin.ext
      change (cut.val + (cycle.length - cut.val - 1) + 1) % cycle.length = 0
      have hcutLt : cut.val < cycle.length := by
        exact cut.isLt
      have hlengthPos := cycle.length_pos
      have heq : cut.val + (cycle.length - cut.val - 1) + 1 =
          cycle.length := by omega
      rw [heq, Nat.mod_self]] at hnext
  exact hnext


def sixVertexDegreeTwoStrandCycleComplementaryArcPair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)))
    (hcut : 0 < cut.val) : SixVertexDirectedComplementaryArcPair T where
  first := sixVertexDegreeTwoStrandCycleForwardArc
    homega heta hdegree seed cut hcut
  second := sixVertexDegreeTwoStrandCycleBackwardArc
    homega heta hdegree seed cut
  first_finish_eq_second_start :=
    sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start
      homega heta hdegree seed cut hcut
  second_finish_eq_first_start :=
    sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start
      homega heta hdegree seed cut hcut
  tail_disjoint := by
    intro i j htail
    let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed
    apply sixVertexFinPrefixIndex_ne_suffixIndex cut i j
    exact cycle.tail_injective htail
  physical_disjoint := by
    intro i j hphysical
    let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed
    apply sixVertexFinPrefixIndex_ne_suffixIndex cut i j
    exact cycle.physical_injective hphysical

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_val_pos
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    0 < (seed.nextPositiveIndex hsame).val := by
  have hne := seed.nextPositiveIndex_ne_zero hsame
  have hval : (seed.nextPositiveIndex hsame).val ≠ 0 := by
    intro hzero
    apply hne
    apply Fin.ext
    simpa [sixVertexDegreeTwoStrandCycleZeroIndex] using hzero
  omega



noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    SixVertexDirectedComplementaryArcPair T :=
  sixVertexDegreeTwoStrandCycleComplementaryArcPair
    homega heta hdegree seed.first (seed.nextPositiveIndex hsame)
      (seed.nextPositiveIndex_val_pos hsame)

end

end StatMech.FrontierD
