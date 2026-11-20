/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedWideEndpoint
import Code.FrontierD.FKRectTorusCrossingEvents



open Set

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

@[simp] theorem fkRectRowReflection_center
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectRowReflection R y.val y = y := by
  apply Fin.ext
  rw [fkRectRowReflection_val]
  have hsub : 2 * y.val + R.height - y.val = y.val + R.height := by
    omega
  rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_center
    (R : FKRectTorus) (v : R.Vertex) :
    fkRectDevelopedReflectionVertexEquiv R v.2.val v = v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowReflection_center R v.2



theorem fkRectOpenGraph_developedReflection_reachable_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Reachable
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectOpenGraph R omega).Reachable x y := by
  exact (fkRectOpenGraphDevelopedReflectionIso R center omega).reachable_iff

theorem fkRectDevelopedReflection_mem_connectionEvent_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    fkRectDevelopedReflectionConfigurationEquiv R center omega ∈
        fkRectTorusConnectionEvent R
          (fkRectDevelopedReflectionVertexEquiv R center x)
          (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      omega ∈ fkRectTorusConnectionEvent R x y :=
  fkRectOpenGraph_developedReflection_reachable_iff
    R center omega x y



theorem fkRectCritical_connectionMass_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real) (x y : R.Vertex) :
    fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R
          (fkRectDevelopedReflectionVertexEquiv R center x)
          (fkRectDevelopedReflectionVertexEquiv R center y)) =
      fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R center
  let A := fkRectTorusConnectionEvent R x y
  let B := fkRectTorusConnectionEvent R
    (fkRectDevelopedReflectionVertexEquiv R center x)
    (fkRectDevelopedReflectionVertexEquiv R center y)
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectDevelopedReflection_mem_connectionEvent_iff
      R center omega x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection
      R center q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]


def fkRectDevelopedReflectionSet (R : FKRectTorus) (center : Nat)
    (S : Set R.Vertex) : Set R.Vertex :=
  fkRectDevelopedReflectionVertexEquiv R center '' S



def fkRectDevelopedReflectionSetEquiv (R : FKRectTorus) (center : Nat)
    (S : Set R.Vertex) : S ≃ fkRectDevelopedReflectionSet R center S where
  toFun v := ⟨fkRectDevelopedReflectionVertexEquiv R center v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨fkRectDevelopedReflectionVertexEquiv R center v.1, by
    rcases v.2 with ⟨w, hw, hreflect⟩
    rw [← hreflect]
    have htwice : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center w) = w := by
      apply Prod.ext
      · rfl
      · exact fkRectRowReflection_involutive R center w.2
    rw [htwice]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.1.2
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.1.2



def fkRectOpenGraphDevelopedReflectionInduceIso
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)).induce
          (fkRectDevelopedReflectionSet R center S) where
  toEquiv := fkRectDevelopedReflectionSetEquiv R center S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_developedReflection_adj
      R center omega x.1 y.1

theorem fkRectConnectedWithin_developedReflection_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)
        (fkRectDevelopedReflectionSet R center S)
        (fkRectDevelopedReflectionSetEquiv R center S x)
        (fkRectDevelopedReflectionSetEquiv R center S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphDevelopedReflectionInduceIso
    R center omega S).reachable_iff



theorem fkRectCritical_connectedWithinMass_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectDevelopedReflectionSet R center S)
          (fkRectDevelopedReflectionSetEquiv R center S x)
          (fkRectDevelopedReflectionSetEquiv R center S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R center
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectDevelopedReflectionSet R center S)
      (fkRectDevelopedReflectionSetEquiv R center S x)
      (fkRectDevelopedReflectionSetEquiv R center S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_developedReflection_iff
      R center omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection
      R center q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]


theorem fkRectCritical_connectedWithinMass_sq_le_reflectedUnion
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Set R.Vertex) (x y : S) :
    let center := y.1.2.val
    let Sr := fkRectDevelopedReflectionSet R center S
    let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} ^ 2 ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega (S ∪ Sr)
          ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩} := by
  dsimp only
  let center := y.1.2.val
  let Sr := fkRectDevelopedReflectionSet R center S
  let xrS : Sr := fkRectDevelopedReflectionSetEquiv R center S x
  let yrS : Sr := fkRectDevelopedReflectionSetEquiv R center S y
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega Sr yrS xrS}
  have hA : IsIncreasing A :=
    fkRectConnectedWithin_isIncreasing R S x y
  have hB : IsIncreasing B :=
    fkRectConnectedWithin_isIncreasing R Sr yrS xrS
  have hmass : fkRectCriticalEventMass R q B =
      fkRectCriticalEventMass R q A := by
    calc
      fkRectCriticalEventMass R q B =
          fkRectCriticalEventMass R q
            {omega | FKRectConnectedWithin R omega Sr xrS yrS} := by
        congr 1
        ext omega
        exact SimpleGraph.reachable_comm
      _ = fkRectCriticalEventMass R q A := by
        simpa [A, Sr, xrS, yrS, center] using
          (fkRectCritical_connectedWithinMass_developedReflection
            R center q S x y)
  have hinter : A ∩ B ⊆
      {omega | FKRectConnectedWithin R omega (S ∪ Sr)
        ⟨x.1, Or.inl x.2⟩
        ⟨xrS.1, Or.inr xrS.2⟩} := by
    intro omega homega
    have hySr : y.1 ∈ Sr := by
      refine ⟨y.1, y.2, ?_⟩
      exact fkRectDevelopedReflectionVertexEquiv_center R y.1
    have hyr : yrS = (⟨y.1, hySr⟩ : Sr) := by
      apply Subtype.ext
      exact fkRectDevelopedReflectionVertexEquiv_center R y.1
    have hBomega : FKRectConnectedWithin R omega Sr
        (⟨y.1, hySr⟩ : Sr) xrS := by
      have hBo := homega.2
      change FKRectConnectedWithin R omega Sr yrS xrS at hBo
      rwa [hyr] at hBo
    apply FKRectConnectedWithin.trans_union R omega
      x.2 y.2 hySr xrS.2 homega.1 hBomega
  calc
    fkRectCriticalEventMass R q A ^ 2 =
        fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B := by rw [hmass, pow_two]
    _ ≤ fkRectCriticalEventMass R q (A ∩ B) :=
      fkRectCriticalEventMass_mul_le_inter R hq hA hB
    _ ≤ fkRectCriticalEventMass R q
          {omega | FKRectConnectedWithin R omega (S ∪ Sr)
            ⟨x.1, Or.inl x.2⟩ ⟨xrS.1, Or.inr xrS.2⟩} :=
      fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq) hinter




theorem fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (x y : R.Vertex) :
    fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) ^ 2 ≤
      fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R x
          (fkRectDevelopedReflectionVertexEquiv R y.2.val x)) := by
  let A := fkRectTorusConnectionEvent R x y
  let xr := fkRectDevelopedReflectionVertexEquiv R y.2.val x
  let B := fkRectTorusConnectionEvent R y xr
  have hA : IsIncreasing A :=
    fkRectTorusConnectionEvent_isIncreasing R x y
  have hB : IsIncreasing B :=
    fkRectTorusConnectionEvent_isIncreasing R y xr
  have hmass : fkRectCriticalEventMass R q B =
      fkRectCriticalEventMass R q A := by
    calc
      fkRectCriticalEventMass R q B =
          fkRectCriticalEventMass R q
            (fkRectTorusConnectionEvent R xr y) := by
        congr 1
        ext omega
        exact SimpleGraph.reachable_comm
      _ = fkRectCriticalEventMass R q A := by
        simpa [A, xr] using
          (fkRectCritical_connectionMass_developedReflection
            R y.2.val q x y)
  have hinter : A ∩ B ⊆ fkRectTorusConnectionEvent R x xr := by
    intro omega homega
    exact homega.1.trans homega.2
  calc
    fkRectCriticalEventMass R q A ^ 2 =
        fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B := by rw [hmass, pow_two]
    _ ≤ fkRectCriticalEventMass R q (A ∩ B) :=
      fkRectCriticalEventMass_mul_le_inter R hq hA hB
    _ ≤ fkRectCriticalEventMass R q
          (fkRectTorusConnectionEvent R x xr) :=
      fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq) hinter

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_fst
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    (fkRectDevelopedReflectionVertexEquiv R center v).1 = v.1 :=
  rfl


def fkRectDevelopedThreeByOneTorusCarrier
    (R : FKRectTorus) (n : Nat) : Set R.Vertex :=
  Set.range fun z : fkRectDevelopedThreeByOneRect n =>
    fkRectDevelopedSquareVertex R n z.1

def fkRectDevelopedThreeByOneCarrierVertex
    (R : FKRectTorus) (n : Nat)
    (z : fkRectDevelopedThreeByOneRect n) :
    fkRectDevelopedThreeByOneTorusCarrier R n :=
  ⟨fkRectDevelopedSquareVertex R n z.1, ⟨z, rfl⟩⟩



def fkRectDevelopedThreeByOneCarrierConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) : Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectDevelopedThreeByOneTorusCarrier R n)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.1)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.2)}

noncomputable def fkRectDevelopedThreeByOneCarrierOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (fkRectDevelopedThreeByOneRect n) →g
      (fkRectOpenGraph R omega).induce
        (fkRectDevelopedThreeByOneTorusCarrier R n) where
  toFun := fkRectDevelopedThreeByOneCarrierVertex R n
  map_rel' := by
    intro z w hzw
    exact (fkRectDevelopedThreeByOneOpenHom
      R n hwidth hheight omega).map_rel hzw

theorem fkRectDevelopedThreeByOneEndpointConnection_subset_carrier
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    fkRectDevelopedThreeByOneEndpointConnectionEvent R n p ⊆
      fkRectDevelopedThreeByOneCarrierConnectionEvent R n p := by
  intro omega hconn
  exact hconn.map (fkRectDevelopedThreeByOneCarrierOpenHom
    R n hwidth hheight omega)

theorem fkRectDevelopedThreeByOneCarrierConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    IsIncreasing
      (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) :=
  fkRectConnectedWithin_isIncreasing R
    (fkRectDevelopedThreeByOneTorusCarrier R n)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.1)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.2)



theorem fkRectDevelopedThreeByOneTorusCarrier_column_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {v : R.Vertex} (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n) :
    1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
  rcases hv with ⟨z, rfl⟩
  have hz := z.2
  change z.1 ∈ StatMech.RSW.Box.rect
    0 (3 * (n : Int)) 0 n at hz
  rw [StatMech.RSW.Box.mem_rect] at hz
  have hpoint := fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight z.2
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx := congrArg Prod.fst hundev
  dsimp [fkRectDevelopedSquarePoint,
    fkRectSquareUndevelopPoint] at hx
  have hhalfLower : 0 ≤ (z.1 0 - z.1 1 + (n : Int)) / 2 := by
    omega
  have hhalfUpper : (z.1 0 - z.1 1 + (n : Int)) / 2 ≤ 2 * n := by
    omega
  have hbounds :
      (1 : Int) ≤ (fkRectDevelopedSquareVertex R n z.1).1.val ∧
        ((fkRectDevelopedSquareVertex R n z.1).1.val : Int) ≤ 4 * n := by
    constructor <;> omega
  exact_mod_cast hbounds


theorem fkRectDevelopedThreeByOneVertex_row_val
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (z : fkRectDevelopedThreeByOneRect n) :
    ((fkRectDevelopedSquareVertex R n z.1).2.val : Int) =
      z.1 0 - z.1 1 + n := by
  have hpoint := fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight z.2
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hy := congrArg Prod.snd hundev
  change ((fkRectDevelopedSquareVertex R n z.1).2.val : Int) =
    (fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z.1)).2 at hy
  rw [hy]
  simp [fkRectDevelopedSquarePoint,
    fkRectSquareUndevelopPoint]
  ring



theorem fkRectDevelopedThreeByOneEndpoint_row_sub
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hp : p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n) :
    ((fkRectDevelopedSquareVertex R n p.2).2.val : Int) -
        (fkRectDevelopedSquareVertex R n p.1).2.val =
      p.2.1 0 - p.1.1 0 - n := by
  have hend :=
    (mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n p).mp hp
  rw [fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.1,
    fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.2,
    hend.1, hend.2]
  ring

theorem fkRectDevelopedReflectionSet_column_bounds
    (R : FKRectTorus) (center left right : Nat)
    (S : Set R.Vertex)
    (hS : ∀ v ∈ S, left ≤ v.1.val ∧ v.1.val ≤ right)
    {v : R.Vertex} (hv : v ∈ fkRectDevelopedReflectionSet R center S) :
    left ≤ v.1.val ∧ v.1.val ≤ right := by
  rcases hv with ⟨w, hw, rfl⟩
  simpa using hS w hw

theorem fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (center : Nat) {v : R.Vertex}
    (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n ∪
      fkRectDevelopedReflectionSet R center
        (fkRectDevelopedThreeByOneTorusCarrier R n)) :
    1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
  rcases hv with hv | hv
  · exact fkRectDevelopedThreeByOneTorusCarrier_column_bounds
      R n hn hwidth hheight hv
  · exact fkRectDevelopedReflectionSet_column_bounds R center 1 (4 * n)
      (fkRectDevelopedThreeByOneTorusCarrier R n)
      (fun w hw => fkRectDevelopedThreeByOneTorusCarrier_column_bounds
        R n hn hwidth hheight hw) hv



theorem FKRectConnectedWithin.exists_walk_support
    (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S)
    (hxy : FKRectConnectedWithin R omega S x y) :
    ∃ w : (fkRectOpenGraph R omega).Walk x.1 y.1,
      ∀ v ∈ w.support, v ∈ S := by
  refine hxy.elim fun p => ?_
  let incl : (fkRectOpenGraph R omega).induce S →g
      fkRectOpenGraph R omega :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} h => h }
  let w := p.map incl
  change (fkRectOpenGraph R omega).Walk x.1 y.1 at w
  refine ⟨w, ?_⟩
  intro v hv
  simp only [w, SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
  rw [← huv]
  exact u.2


theorem fkRectDevelopedThreeByOne_reflectedCarrierConnection_exists_walk
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hconn :
      let S := fkRectDevelopedThreeByOneTorusCarrier R n
      let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
      let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
      let center := y.1.2.val
      let Sr := fkRectDevelopedReflectionSet R center S
      let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
      FKRectConnectedWithin R omega (S ∪ Sr)
        ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩) :
    let S := fkRectDevelopedThreeByOneTorusCarrier R n
    let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
    let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
    let center := y.1.2.val
    let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
    ∃ w : (fkRectOpenGraph R omega).Walk x.1 xr,
      ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
  dsimp only at hconn ⊢
  let S : Set R.Vertex := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  let center := y.1.2.val
  let Sr : Set R.Vertex := fkRectDevelopedReflectionSet R center S
  obtain ⟨w, hw⟩ := FKRectConnectedWithin.exists_walk_support
    R omega (S ∪ Sr)
    (⟨x.1, Or.inl x.2⟩ : (S ∪ Sr : Set R.Vertex))
    (⟨fkRectDevelopedReflectionVertexEquiv R center x.1,
      Or.inr ⟨x.1, x.2, rfl⟩⟩ : (S ∪ Sr : Set R.Vertex)) hconn
  refine ⟨w, ?_⟩
  intro v hv
  exact fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
    R n hn hwidth hheight center (hw v hv)




theorem fkRectCritical_developedThreeByOne_exists_reflectedRowConnection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      let x := fkRectDevelopedSquareVertex R n p.1
      let y := fkRectDevelopedSquareVertex R n p.2
      (1 / (2 * (1 + q)) /
          (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2 ≤
        fkRectCriticalEventMass R q
          (fkRectTorusConnectionEvent R x
            (fkRectDevelopedReflectionVertexEquiv R y.2.val x)) := by
  obtain ⟨p, hp, havg⟩ :=
    fkRectCritical_developedThreeByOne_exists_torus_endpoint_ge
      R n hn hwidth hheight hq
  refine ⟨p, hp, ?_⟩
  let x := fkRectDevelopedSquareVertex R n p.1
  let y := fkRectDevelopedSquareVertex R n p.2
  let M : Real := (((3 * n + 1) ^ 2 : Nat) : Real)
  let a : Real := 1 / (2 * (1 + q)) / M
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hlower : a ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionEvent R x y) := by
    rw [show a = 1 / (2 * (1 + q)) / M by rfl,
      div_le_iff₀ hM]
    simpa [M, x, y, mul_comm,
      fkRectDevelopedThreeByOneTorusEndpointConnectionEvent] using havg
  have hsq : a ^ 2 ≤
      fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R x y) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hlower 2
  exact hsq.trans
    (fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass
      R hq x y)




theorem fkRectCritical_developedThreeByOne_exists_reflectedCarrierConnection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      let S := fkRectDevelopedThreeByOneTorusCarrier R n
      let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
      let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
      let center := y.1.2.val
      let Sr := fkRectDevelopedReflectionSet R center S
      let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
      (1 / (2 * (1 + q)) /
          (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2 ≤
        fkRectCriticalEventMass R q
          {omega | FKRectConnectedWithin R omega (S ∪ Sr)
            ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩} := by
  obtain ⟨p, hp, havg⟩ :=
    fkRectCritical_developedThreeByOne_exists_endpoint_ge
      R n hn (by omega) (by omega) hq
  refine ⟨p, hp, ?_⟩
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  let M : Real := (((3 * n + 1) ^ 2 : Nat) : Real)
  let a : Real := 1 / (2 * (1 + q)) / M
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hplanar : a ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
    rw [show a = 1 / (2 * (1 + q)) / M by rfl,
      div_le_iff₀ hM]
    simpa [M, mul_comm] using havg
  have hcarrier : a ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) :=
    hplanar.trans (fkRectCriticalEventMass_mono R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedThreeByOneEndpointConnection_subset_carrier
        R n hwidth hheight p))
  have hsq : a ^ 2 ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcarrier 2
  exact hsq.trans (by
    simpa [S, x, y,
      fkRectDevelopedThreeByOneCarrierConnectionEvent] using
      (fkRectCritical_connectedWithinMass_sq_le_reflectedUnion
        R hq S x y))

end

end StatMech.FrontierD
