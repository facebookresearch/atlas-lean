/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectOrientedEvenRowBlock



open Set SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectColumnTranslate (R : FKRectTorus) (s : Int)
    (x : Fin R.width) : Fin R.width :=
  fkRectIntModFin R.width_pos ((x.val : Int) + s)

theorem fkRectColumnTranslate_neg_left
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R (-s) (fkRectColumnTranslate R s x) = x := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.width).mp
    simp only [fkRectColumnTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectColumnTranslate R (-s) (fkRectColumnTranslate R s x)).isLt
  · exact x.isLt

theorem fkRectColumnTranslate_neg_right
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R s (fkRectColumnTranslate R (-s) x) = x := by
  simpa only [neg_neg] using fkRectColumnTranslate_neg_left R (-s) x


def fkRectColumnTranslationEquiv (R : FKRectTorus) (s : Int) :
    Fin R.width ≃ Fin R.width where
  toFun := fkRectColumnTranslate R s
  invFun := fkRectColumnTranslate R (-s)
  left_inv := fkRectColumnTranslate_neg_left R s
  right_inv := fkRectColumnTranslate_neg_right R s

@[simp] theorem fkRectColumnTranslationEquiv_apply
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslationEquiv R s x = fkRectColumnTranslate R s x := rfl

private theorem fkRectColumn_cyclicPred_cast (R : FKRectTorus)
    (x : Fin R.width) :
    ((SixVertexArrows.cyclicPred R.width_pos x).val : ZMod R.width) =
      (x.val : ZMod R.width) - 1 := by
  rw [fkRectCyclicPred_val]
  split <;> rename_i h
  · rw [Nat.cast_sub (by omega : 1 ≤ R.width)]
    push_cast
    rw [h]
    simp
  · rw [Nat.cast_sub (by omega : 1 ≤ x.val)]
    push_cast
    ring

theorem fkRectColumnTranslate_cyclicPred
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R s
        (SixVertexArrows.cyclicPred R.width_pos x) =
      SixVertexArrows.cyclicPred R.width_pos
        (fkRectColumnTranslate R s x) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.width).mp
    rw [show ((fkRectColumnTranslate R s
        (SixVertexArrows.cyclicPred R.width_pos x)).val : ZMod R.width) =
        (SixVertexArrows.cyclicPred R.width_pos x).val + s by
      simpa [fkRectColumnTranslate] using fkRectIntModFin_cast R.width_pos
        ((SixVertexArrows.cyclicPred R.width_pos x).val + s)]
    rw [fkRectColumn_cyclicPred_cast, fkRectColumn_cyclicPred_cast]
    rw [show ((fkRectColumnTranslate R s x).val : ZMod R.width) =
        (x.val : Int) + s by
      simpa [fkRectColumnTranslate] using fkRectIntModFin_cast R.width_pos
        ((x.val : Int) + s)]
    push_cast
    ring
  · exact (fkRectColumnTranslate R s
      (SixVertexArrows.cyclicPred R.width_pos x)).isLt
  · exact (SixVertexArrows.cyclicPred R.width_pos
      (fkRectColumnTranslate R s x)).isLt


def fkRectColumnTranslationVertexEquiv
    (R : FKRectTorus) (s : Int) : R.Vertex ≃ R.Vertex :=
  (fkRectColumnTranslationEquiv R s).prodCongr
    (Equiv.refl (Fin R.height))

@[simp] theorem fkRectColumnTranslationVertexEquiv_apply
    (R : FKRectTorus) (s : Int) (v : R.Vertex) :
    fkRectColumnTranslationVertexEquiv R s v =
      (fkRectColumnTranslate R s v.1, v.2) := rfl


def fkRectColumnTranslationEdgeEquiv
    (R : FKRectTorus) (s : Int) : R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((fkRectColumnTranslationEquiv R s).prodCongr
      (Equiv.refl (Fin R.height)))

@[simp] theorem fkRectColumnTranslationEdgeEquiv_apply
    (R : FKRectTorus) (s : Int) (a : R.EdgeIndex) :
    fkRectColumnTranslationEdgeEquiv R s a =
      (a.1, (fkRectColumnTranslate R s a.2.1, a.2.2)) := rfl


theorem fkRectTorusIndexedEdge_columnTranslation
    (R : FKRectTorus) (s : Int) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectColumnTranslationEdgeEquiv R s a) =
      Sym2.map (fkRectColumnTranslationVertexEquiv R s)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectColumnTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, if_true,
        fkRectColumnTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectColumnTranslate_cyclicPred]
    · simp only [fkRectColumnTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
        fkRectColumnTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectColumnTranslate_cyclicPred]
  · simp [fkRectTorusIndexedEdge]


def fkRectColumnTranslationConfigurationEquiv
    (R : FKRectTorus) (s : Int) : R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectColumnTranslationEdgeEquiv R s)
    (Equiv.refl Bool)

@[simp] theorem fkRectColumnTranslationConfigurationEquiv_apply
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectColumnTranslationConfigurationEquiv R s omega a =
      omega ((fkRectColumnTranslationEdgeEquiv R s).symm a) := rfl

theorem fkRectOpenGraph_columnTranslation_adj
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectColumnTranslationConfigurationEquiv R s omega)).Adj
        (fkRectColumnTranslationVertexEquiv R s x)
        (fkRectColumnTranslationVertexEquiv R s y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R s).symm a
    refine ⟨b, haopen, ?_⟩
    have htranslate := fkRectTorusIndexedEdge_columnTranslation R s b
    rw [(fkRectColumnTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R s a, ?_, ?_⟩
    · change omega ((fkRectColumnTranslationEdgeEquiv R s).symm
        (fkRectColumnTranslationEdgeEquiv R s a)) = true
      rwa [(fkRectColumnTranslationEdgeEquiv R s).symm_apply_apply]
    · rw [fkRectTorusIndexedEdge_columnTranslation R s, ha, Sym2.map_mk]

def fkRectOpenGraphColumnTranslationIso
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectColumnTranslationConfigurationEquiv R s omega) where
  toEquiv := fkRectColumnTranslationVertexEquiv R s
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_columnTranslation_adj R s omega x y

theorem fkRectOpenEdgeCount_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectColumnTranslationEdgeEquiv R s
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, E.symm_apply_apply b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    change omega (E.symm (E b)) = true
    rwa [E.symm_apply_apply]

theorem fkRectNumClusters_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphColumnTranslationIso
      R s omega).connectedComponentEquiv).symm

theorem fkRectCriticalReducedWeight_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_columnTranslation,
    fkRectNumClusters_columnTranslation]

theorem fkRectCriticalReducedZ_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) :
    (∑ omega : R.Configuration,
        fkRectCriticalReducedWeight R q
          (fkRectColumnTranslationConfigurationEquiv R s omega)) =
      fkRectCriticalReducedZ R q := by
  simp only [fkRectCriticalReducedWeight_columnTranslation]
  rfl

theorem fkRectCriticalRandomClusterProb_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_columnTranslation]


theorem fkRectCriticalEventMass_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      fkRectCriticalEventMass R q
        ((fkRectColumnTranslationConfigurationEquiv R s) '' A) := by
  classical
  let C := fkRectColumnTranslationConfigurationEquiv R s
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    (C '' A).indicator
      (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ C '' A ↔ omega ∈ A := by
    constructor
    · rintro ⟨eta, heta, heq⟩
      exact C.injective heq ▸ heta
    · intro homega
      exact ⟨omega, homega, rfl⟩
  have hprob := fkRectCriticalRandomClusterProb_columnTranslation
    R s q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun h => hA (hmem.mp h))]


def fkRectColumnTranslationSet
    (R : FKRectTorus) (s : Int) (S : Set R.Vertex) : Set R.Vertex :=
  fkRectColumnTranslationVertexEquiv R s '' S


def fkRectColumnTranslationSetEquiv
    (R : FKRectTorus) (s : Int) (S : Set R.Vertex) :
    S ≃ fkRectColumnTranslationSet R s S where
  toFun v := ⟨fkRectColumnTranslationVertexEquiv R s v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectColumnTranslationVertexEquiv R s).symm v.1, by
    rcases v.2 with ⟨w, hw, htranslate⟩
    rw [← htranslate, Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectColumnTranslationVertexEquiv R s).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectColumnTranslationVertexEquiv R s).apply_symm_apply v.1

def fkRectOpenGraphColumnTranslationInduceIso
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectColumnTranslationConfigurationEquiv R s omega)).induce
          (fkRectColumnTranslationSet R s S) where
  toEquiv := fkRectColumnTranslationSetEquiv R s S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_columnTranslation_adj R s omega x.1 y.1

theorem fkRectConnectedWithin_columnTranslation_iff
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectColumnTranslationConfigurationEquiv R s omega)
        (fkRectColumnTranslationSet R s S)
        (fkRectColumnTranslationSetEquiv R s S x)
        (fkRectColumnTranslationSetEquiv R s S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphColumnTranslationInduceIso
    R s omega S).reachable_iff

theorem fkRectCritical_connectedWithinMass_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnTranslationSet R s S)
          (fkRectColumnTranslationSetEquiv R s S x)
          (fkRectColumnTranslationSetEquiv R s S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectColumnTranslationConfigurationEquiv R s
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectColumnTranslationSet R s S)
      (fkRectColumnTranslationSetEquiv R s S x)
      (fkRectColumnTranslationSetEquiv R s S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_columnTranslation_iff R s omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_columnTranslation R s q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]




theorem fkRectTorusIndexedEdge_columnSucc (R : FKRectTorus)
    (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectColumnTranslationEdgeEquiv R 1 a) =
      Sym2.map (fkRectColumnTranslationVertexEquiv R 1)
        (fkRectTorusIndexedEdge R a) :=
  fkRectTorusIndexedEdge_columnTranslation R 1 a

theorem fkRectTorusGraph_adj_columnSucc (R : FKRectTorus)
    (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectColumnTranslationVertexEquiv R 1 x)
        (fkRectColumnTranslationVertexEquiv R 1 y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R 1).symm a
    refine ⟨b, ?_⟩
    have htranslate := fkRectTorusIndexedEdge_columnSucc R b
    rw [(fkRectColumnTranslationEdgeEquiv R 1).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R 1).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R 1 a, ?_⟩
    rw [fkRectTorusIndexedEdge_columnSucc R, ha, Sym2.map_mk]

theorem fkRectOpenGraph_columnSucc_adj
    (R : FKRectTorus) (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectColumnTranslationConfigurationEquiv R 1 omega)).Adj
        (fkRectColumnTranslationVertexEquiv R 1 x)
        (fkRectColumnTranslationVertexEquiv R 1 y) ↔
      (fkRectOpenGraph R omega).Adj x y :=
  fkRectOpenGraph_columnTranslation_adj R 1 omega x y

theorem fkRectCriticalRandomClusterProb_columnSucc
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectColumnTranslationConfigurationEquiv R 1 omega) =
      fkRectCriticalRandomClusterProb R q omega :=
  fkRectCriticalRandomClusterProb_columnTranslation R 1 q omega

theorem fkRectConnectedWithin_columnSucc_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectColumnTranslationConfigurationEquiv R 1 omega)
        (fkRectColumnTranslationSet R 1 S)
        (fkRectColumnTranslationSetEquiv R 1 S x)
        (fkRectColumnTranslationSetEquiv R 1 S y) ↔
      FKRectConnectedWithin R omega S x y :=
  fkRectConnectedWithin_columnTranslation_iff R 1 omega S x y

theorem fkRectCritical_connectedWithinMass_columnSucc
    (R : FKRectTorus) (q : Real) (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnTranslationSet R 1 S)
          (fkRectColumnTranslationSetEquiv R 1 S x)
          (fkRectColumnTranslationSetEquiv R 1 S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} :=
  fkRectCritical_connectedWithinMass_columnTranslation R 1 q S x y


structure FKRectPositiveBandOrientedBlock
    (R : FKRectTorus) (q : Real) (scale : Nat) where
  carrier : Set R.Vertex
  start : carrier
  finish : carrier
  step : Nat
  step_even : Even step
  step_scale : scale ≤ step + 2
  step_upper : step ≤ 16 * scale + 2
  translate_start :
    fkRectEvenRowTranslationVertexEquiv R step start.1 = finish.1
  massFloor : Real
  massFloor_nonneg : 0 ≤ massFloor
  mass_lower : massFloor ≤
    fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega carrier start finish}
  column_bound : ∀ v ∈ carrier,
    1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1
  row_bound : ∀ v ∈ carrier,
    1 ≤ v.2.val ∧ v.2.val ≤ 24 * scale + 4

theorem fkRectColumnTranslate_one_val_of_lt
    (R : FKRectTorus) (x : Fin R.width)
    (hlt : x.val + 1 < R.width) :
    (fkRectColumnTranslate R 1 x).val = x.val + 1 := by
  change (((x.val : Int) + 1).natMod R.width : Nat) = x.val + 1
  rw [Int.natMod, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hlt)]
  exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ (x.val : Int) + 1 by omega)

theorem fkRectEvenRowTranslation_columnTranslation_comm
    (R : FKRectTorus) (step : Nat) (s : Int) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R step
        (fkRectColumnTranslationVertexEquiv R s v) =
      fkRectColumnTranslationVertexEquiv R s
        (fkRectEvenRowTranslationVertexEquiv R step v) := by
  rfl



noncomputable def FKRectPositiveRowOrientedBlock.columnSuccBand
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveRowOrientedBlock R q scale)
    (hwidth : 4 * scale + 1 < R.width) :
    FKRectPositiveBandOrientedBlock R q scale := by
  let S := fkRectColumnTranslationSet R 1 B.block.carrier
  let x : S := fkRectColumnTranslationSetEquiv
    R 1 B.block.carrier B.block.start
  let y : S := fkRectColumnTranslationSetEquiv
    R 1 B.block.carrier B.block.finish
  refine
    { carrier := S
      start := x
      finish := y
      step := B.block.step
      step_even := B.block.step_even
      step_scale := B.block.step_scale
      step_upper := B.block.step_upper
      translate_start := ?_
      massFloor := B.block.massFloor
      massFloor_nonneg := B.block.massFloor_nonneg
      mass_lower := ?_
      column_bound := ?_
      row_bound := ?_ }
  · change fkRectEvenRowTranslationVertexEquiv R B.block.step
        (fkRectColumnTranslationVertexEquiv R 1 B.block.start.1) =
      fkRectColumnTranslationVertexEquiv R 1 B.block.finish.1
    rw [fkRectEvenRowTranslation_columnTranslation_comm,
      B.block.translate_start]
  · rw [show fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega B.block.carrier
          B.block.start B.block.finish} by
      simpa [S, x, y] using
        (fkRectCritical_connectedWithinMass_columnTranslation
          R 1 q B.block.carrier B.block.start B.block.finish)]
    exact B.block.mass_lower
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩
    have hwcol := B.block.column_bound w hw
    have hlt : w.1.val + 1 < R.width := by omega
    rw [fkRectColumnTranslationVertexEquiv_apply,
      fkRectColumnTranslate_one_val_of_lt R w.1 hlt]
    change 1 ≤ w.1.val + 1 ∧ w.1.val + 1 ≤ 4 * scale + 1
    omega
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩
    simpa [fkRectColumnTranslationVertexEquiv_apply] using B.row_bound w hw

end

end StatMech.FrontierD
