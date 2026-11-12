/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedAxisSource



open Set SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section


def fkRectRowTranslate (R : FKRectTorus) (s : Int)
    (y : Fin R.height) : Fin R.height :=
  fkRectIntModFin R.height_pos ((y.val : Int) + s)

theorem fkRectRowTranslate_neg_left
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R (-s) (fkRectRowTranslate R s y) = y := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    simp only [fkRectRowTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectRowTranslate R (-s) (fkRectRowTranslate R s y)).isLt
  · exact y.isLt

theorem fkRectRowTranslate_neg_right
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R s (fkRectRowTranslate R (-s) y) = y := by
  simpa only [neg_neg] using fkRectRowTranslate_neg_left R (-s) y


def fkRectRowTranslationEquiv (R : FKRectTorus) (s : Int) :
    Fin R.height ≃ Fin R.height where
  toFun := fkRectRowTranslate R s
  invFun := fkRectRowTranslate R (-s)
  left_inv := fkRectRowTranslate_neg_left R s
  right_inv := fkRectRowTranslate_neg_right R s

@[simp] theorem fkRectRowTranslationEquiv_apply
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslationEquiv R s y = fkRectRowTranslate R s y := rfl

theorem fkRectRowTranslate_nat_val
    (R : FKRectTorus) (s : Nat) (y : Fin R.height) :
    (fkRectRowTranslate R s y).val = (y.val + s) % R.height := by
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R s y).val : ZMod R.height) =
        (y.val : Int) + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((y.val : Int) + s)]
    simp
  · exact (fkRectRowTranslate R s y).isLt
  · exact Nat.mod_lt _ R.height_pos

@[simp] theorem fkRectRowTranslate_zero
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectRowTranslate R 0 y = y := by
  change fkRectRowTranslate R (0 : Nat) y = y
  apply Fin.ext
  rw [fkRectRowTranslate_nat_val]
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt y.isLt


theorem fkRectRowTranslate_even_iff
    (R : FKRectTorus) (s : Nat) (hs : Even s) (y : Fin R.height) :
    Even (fkRectRowTranslate R s y).val ↔ Even y.val := by
  rw [fkRectRowTranslate_nat_val,
    Even.mod_even_iff R.height_even, Nat.even_add]
  simp [hs]

private theorem fkRectCyclicPred_cast (R : FKRectTorus)
    (y : Fin R.height) :
    ((SixVertexArrows.cyclicPred R.height_pos y).val : ZMod R.height) =
      (y.val : ZMod R.height) - 1 := by
  rw [fkRectCyclicPred_val]
  split <;> rename_i h
  · rw [Nat.cast_sub (by omega : 1 ≤ R.height)]
    push_cast
    simp
    rw [h]
    simp
  · rw [Nat.cast_sub (by omega : 1 ≤ y.val)]
    push_cast
    ring


theorem fkRectRowTranslate_cyclicPred
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R s
        (SixVertexArrows.cyclicPred R.height_pos y) =
      SixVertexArrows.cyclicPred R.height_pos
        (fkRectRowTranslate R s y) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R s
        (SixVertexArrows.cyclicPred R.height_pos y)).val :
          ZMod R.height) =
        (SixVertexArrows.cyclicPred R.height_pos y).val + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((SixVertexArrows.cyclicPred R.height_pos y).val + s)]
    rw [fkRectCyclicPred_cast, fkRectCyclicPred_cast]
    rw [show ((fkRectRowTranslate R s y).val : ZMod R.height) =
        (y.val : Int) + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((y.val : Int) + s)]
    push_cast
    ring
  · exact (fkRectRowTranslate R s
      (SixVertexArrows.cyclicPred R.height_pos y)).isLt
  · exact (SixVertexArrows.cyclicPred R.height_pos
      (fkRectRowTranslate R s y)).isLt


theorem fkRectRowTranslate_add
    (R : FKRectTorus) (a b : Nat) (y : Fin R.height) :
    fkRectRowTranslate R a (fkRectRowTranslate R b y) =
      fkRectRowTranslate R (a + b) y := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    simp only [fkRectRowTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast, fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectRowTranslate R a (fkRectRowTranslate R b y)).isLt
  · exact (fkRectRowTranslate R (a + b) y).isLt


def fkRectEvenRowTranslationVertexEquiv
    (R : FKRectTorus) (s : Nat) : R.Vertex ≃ R.Vertex :=
  (Equiv.refl (Fin R.width)).prodCongr
    (fkRectRowTranslationEquiv R s)

@[simp] theorem fkRectEvenRowTranslationVertexEquiv_apply
    (R : FKRectTorus) (s : Nat) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R s v =
      (v.1, fkRectRowTranslate R s v.2) := rfl

theorem fkRectEvenRowTranslationVertexEquiv_add
    (R : FKRectTorus) (a b : Nat) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R a
        (fkRectEvenRowTranslationVertexEquiv R b v) =
      fkRectEvenRowTranslationVertexEquiv R (a + b) v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowTranslate_add R a b v.2

@[simp] theorem fkRectEvenRowTranslationVertexEquiv_zero
    (R : FKRectTorus) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R 0 v = v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowTranslate_zero R v.2


def fkRectEvenRowTranslationEdgeEquiv
    (R : FKRectTorus) (s : Nat) : R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((Equiv.refl (Fin R.width)).prodCongr
      (fkRectRowTranslationEquiv R s))

@[simp] theorem fkRectEvenRowTranslationEdgeEquiv_apply
    (R : FKRectTorus) (s : Nat) (a : R.EdgeIndex) :
    fkRectEvenRowTranslationEdgeEquiv R s a =
      (a.1, (a.2.1, fkRectRowTranslate R s a.2.2)) := rfl


theorem fkRectTorusIndexedEdge_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectEvenRowTranslationEdgeEquiv R s a) =
      Sym2.map (fkRectEvenRowTranslationVertexEquiv R s)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · have hparity := fkRectRowTranslate_even_iff R s hs y
    by_cases hy : Even y.val
    · have hty : Even (fkRectRowTranslate R s y).val := hparity.mpr hy
      simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, hty,
        if_true, fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectRowTranslate_cyclicPred]
    · have hty : ¬ Even (fkRectRowTranslate R s y).val := by
        simpa [hparity] using hy
      simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, hty,
        fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectRowTranslate_cyclicPred]
  · simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
      fkRectTorusIndexedEdge, if_true,
      fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
    rw [fkRectRowTranslate_cyclicPred]


theorem fkRectTorusGraph_adj_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectEvenRowTranslationVertexEquiv R s x)
        (fkRectEvenRowTranslationVertexEquiv R s y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectEvenRowTranslationEdgeEquiv R s).symm a
    refine ⟨b, ?_⟩
    have htranslate :=
      fkRectTorusIndexedEdge_evenRowTranslation R s hs b
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectEvenRowTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectEvenRowTranslationEdgeEquiv R s a, ?_⟩
    rw [fkRectTorusIndexedEdge_evenRowTranslation R s hs, ha,
      Sym2.map_mk]


def fkRectEvenRowTranslationConfigurationEquiv
    (R : FKRectTorus) (s : Nat) : R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectEvenRowTranslationEdgeEquiv R s)
    (Equiv.refl Bool)

@[simp] theorem fkRectEvenRowTranslationConfigurationEquiv_apply
    (R : FKRectTorus) (s : Nat) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectEvenRowTranslationConfigurationEquiv R s omega a =
      omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm a) := rfl

theorem fkRectOpenGraph_evenRowTranslation_adj
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectEvenRowTranslationConfigurationEquiv R s omega)).Adj
        (fkRectEvenRowTranslationVertexEquiv R s x)
        (fkRectEvenRowTranslationVertexEquiv R s y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectEvenRowTranslationEdgeEquiv R s).symm a
    refine ⟨b, haopen, ?_⟩
    have htranslate :=
      fkRectTorusIndexedEdge_evenRowTranslation R s hs b
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectEvenRowTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectEvenRowTranslationEdgeEquiv R s a, ?_, ?_⟩
    · change omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm
        (fkRectEvenRowTranslationEdgeEquiv R s a)) = true
      rwa [(fkRectEvenRowTranslationEdgeEquiv R s).symm_apply_apply]
    · rw [fkRectTorusIndexedEdge_evenRowTranslation R s hs, ha,
        Sym2.map_mk]

def fkRectOpenGraphEvenRowTranslationIso
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) where
  toEquiv := fkRectEvenRowTranslationVertexEquiv R s
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_evenRowTranslation_adj R s hs omega x y

theorem fkRectOpenEdgeCount_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectEvenRowTranslationEdgeEquiv R s
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

theorem fkRectNumClusters_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphEvenRowTranslationIso
      R s hs omega).connectedComponentEquiv).symm

theorem fkRectCriticalReducedWeight_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_evenRowTranslation,
    fkRectNumClusters_evenRowTranslation R s hs]

theorem fkRectCriticalRandomClusterProb_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_evenRowTranslation R s hs]


def fkRectEvenRowTranslationSet
    (R : FKRectTorus) (s : Nat) (S : Set R.Vertex) : Set R.Vertex :=
  fkRectEvenRowTranslationVertexEquiv R s '' S

def fkRectEvenRowTranslationSetEquiv
    (R : FKRectTorus) (s : Nat) (S : Set R.Vertex) :
    S ≃ fkRectEvenRowTranslationSet R s S where
  toFun v := ⟨fkRectEvenRowTranslationVertexEquiv R s v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectEvenRowTranslationVertexEquiv R s).symm v.1, by
    rcases v.2 with ⟨w, hw, htranslate⟩
    rw [← htranslate, Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectEvenRowTranslationVertexEquiv R s).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectEvenRowTranslationVertexEquiv R s).apply_symm_apply v.1

def fkRectOpenGraphEvenRowTranslationInduceIso
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)).induce
          (fkRectEvenRowTranslationSet R s S) where
  toEquiv := fkRectEvenRowTranslationSetEquiv R s S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_evenRowTranslation_adj
      R s hs omega x.1 y.1

theorem fkRectConnectedWithin_evenRowTranslation_iff
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)
        (fkRectEvenRowTranslationSet R s S)
        (fkRectEvenRowTranslationSetEquiv R s S x)
        (fkRectEvenRowTranslationSetEquiv R s S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphEvenRowTranslationInduceIso
    R s hs omega S).reachable_iff



theorem fkRectCritical_connectedWithinMass_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectEvenRowTranslationSet R s S)
          (fkRectEvenRowTranslationSetEquiv R s S x)
          (fkRectEvenRowTranslationSetEquiv R s S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectEvenRowTranslationConfigurationEquiv R s
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectEvenRowTranslationSet R s S)
      (fkRectEvenRowTranslationSetEquiv R s S x)
      (fkRectEvenRowTranslationSetEquiv R s S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_evenRowTranslation_iff
      R s hs omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_evenRowTranslation
      R s hs q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]

end

end StatMech.FrontierD
