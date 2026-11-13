/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.SurfaceKacWardArf
import Code.FrontierA.KacWardForest














open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

def surfaceSpinLinearParity {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Fin 2 :=
  ∑ i, (lambda.1 i * h.1 i + lambda.2 i * h.2 i)

theorem surfaceSpinLinearParity_local_add
    (a b x y x' y' : Fin 2) :
    a * (x + x') + b * (y + y') =
      (a * x + b * y) + (a * x' + b * y') := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    fin_cases x' <;> fin_cases y' <;> decide

theorem surfaceSpinLinearParity_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceSpinLinearParity lambda (h + k) =
      surfaceSpinLinearParity lambda h + surfaceSpinLinearParity lambda k := by
  unfold surfaceSpinLinearParity
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact surfaceSpinLinearParity_local_add
    (lambda.1 i) (lambda.2 i) (h.1 i) (h.2 i) (k.1 i) (k.2 i)

def surfaceBaseQuadraticParity {g : Nat} (h : SurfaceHomology g) : Fin 2 :=
  ∑ i, h.1 i * h.2 i

theorem surfaceQuadraticParity_eq_base_add_linear {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    surfaceQuadraticParity lambda h =
      surfaceBaseQuadraticParity h + surfaceSpinLinearParity lambda h := by
  unfold surfaceQuadraticParity surfaceBaseQuadraticParity surfaceSpinLinearParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

@[simp] theorem surfaceQuadraticParity_zero {g : Nat} (h : SurfaceHomology g) :
    surfaceQuadraticParity (0 : SurfaceSpinStructure g) h =
      surfaceBaseQuadraticParity h := by
  rw [surfaceQuadraticParity_eq_base_add_linear]
  simp [surfaceSpinLinearParity]

def surfaceHomologyCharacter {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Complex :=
  (surfaceParitySign (surfaceSpinLinearParity lambda h) : Complex)

@[simp] theorem surfaceHomologyCharacter_zero {g : Nat}
    (lambda : SurfaceSpinStructure g) :
    surfaceHomologyCharacter lambda 0 = 1 := by
  simp [surfaceHomologyCharacter, surfaceSpinLinearParity]

theorem surfaceHomologyCharacter_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceHomologyCharacter lambda (h + k) =
      surfaceHomologyCharacter lambda h * surfaceHomologyCharacter lambda k := by
  unfold surfaceHomologyCharacter
  rw [surfaceSpinLinearParity_add, surfaceParitySign_add]
  push_cast
  rfl

theorem surfaceHomologyCharacter_finset_sum {g : Nat}
    {ι : Type*} [DecidableEq ι] (lambda : SurfaceSpinStructure g)
    (S : Finset ι) (f : ι → SurfaceHomology g) :
    surfaceHomologyCharacter lambda (∑ i ∈ S, f i) =
      ∏ i ∈ S, surfaceHomologyCharacter lambda (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        surfaceHomologyCharacter_add, ih]

noncomputable def surfaceSubgraphHomology {g : Nat} {V : Type*}
    (edgeClass : Sym2 V → SurfaceHomology g) (F : Finset (Sym2 V)) :
    SurfaceHomology g :=
  ∑ edge ∈ F, edgeClass edge

noncomputable def surfaceTwistedEdgeWeight {g : Nat} {V : Type*}
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    Sym2 V → Complex :=
  fun edge => surfaceHomologyCharacter lambda (edgeClass edge) * weight edge

theorem prod_surfaceTwistedEdgeWeight {g : Nat} {V : Type*}
    [DecidableEq V] (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex)
    (F : Finset (Sym2 V)) :
    (∏ edge ∈ F, surfaceTwistedEdgeWeight edgeClass lambda weight edge) =
      surfaceHomologyCharacter lambda (surfaceSubgraphHomology edgeClass F) *
        ∏ edge ∈ F, weight edge := by
  unfold surfaceTwistedEdgeWeight surfaceSubgraphHomology
  rw [Finset.prod_mul_distrib,
    surfaceHomologyCharacter_finset_sum]

noncomputable def surfaceQuadraticEvenPolynomial {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) : Complex :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    (surfaceParitySign
      (surfaceQuadraticParity lambda (surfaceSubgraphHomology edgeClass F)) : Complex) *
      ∏ edge ∈ F, weight edge

theorem surfaceParitySign_quadratic_twist {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    (surfaceParitySign (surfaceQuadraticParity lambda h) : Complex) =
      (surfaceParitySign (surfaceBaseQuadraticParity h) : Complex) *
        surfaceHomologyCharacter lambda h := by
  rw [surfaceQuadraticParity_eq_base_add_linear, surfaceParitySign_add]
  unfold surfaceHomologyCharacter
  push_cast
  rfl

theorem surfaceQuadraticEvenPolynomial_twist {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g)
        (surfaceTwistedEdgeWeight edgeClass lambda weight) =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  unfold surfaceQuadraticEvenPolynomial
  apply Finset.sum_congr rfl
  intro F hF
  rw [prod_surfaceTwistedEdgeWeight, surfaceQuadraticParity_zero,
    surfaceParitySign_quadratic_twist]
  ring

noncomputable def surfaceTwistedKacWardMatrix {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    Matrix G.Dart G.Dart Complex :=
  kwGraphTransition G (surfaceTwistedEdgeWeight edgeClass lambda weight) phase

theorem surfaceTwistedKacWardMatrix_apply {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex)
    (d e : G.Dart) :
    surfaceTwistedKacWardMatrix G phase edgeClass lambda weight d e =
      if d.snd = e.fst ∧ d.edge ≠ e.edge then
        surfaceHomologyCharacter lambda (edgeClass d.edge) *
          weight d.edge * phase d e
      else 0 := by
  simp [surfaceTwistedKacWardMatrix, kwGraphTransition,
    surfaceTwistedEdgeWeight, mul_assoc]



theorem surface_twisted_kacWard_det_square_of_base {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (hbase : ∀ w : Sym2 V → Complex,
      (1 - kwGraphTransition G w phase).det =
        surfaceQuadraticEvenPolynomial G edgeClass
          (0 : SurfaceSpinStructure g) w ^ 2)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Complex) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  unfold surfaceTwistedKacWardMatrix
  rw [hbase, surfaceQuadraticEvenPolynomial_twist]


noncomputable def surfaceGraphSectorWeight {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (weight : Sym2 V → Real) (h : SurfaceHomology g) : Real :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph with
      surfaceSubgraphHomology edgeClass F = h,
    ∏ edge ∈ F, weight edge



theorem surfaceTwistedSectorRoot_graphSectorWeight {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (weight : Sym2 V → Real) (lambda : SurfaceSpinStructure g) :
    surfaceTwistedSectorRoot
        (surfaceGraphSectorWeight G edgeClass weight) lambda =
      ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
        surfaceParitySign
          (surfaceQuadraticParity lambda
            (surfaceSubgraphHomology edgeClass F)) *
          ∏ edge ∈ F, weight edge := by
  unfold surfaceTwistedSectorRoot surfaceGraphSectorWeight
  calc
    (∑ h : SurfaceHomology g,
        surfaceParitySign (surfaceQuadraticParity lambda h) *
          ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph with
              surfaceSubgraphHomology edgeClass F = h,
            ∏ edge ∈ F, weight edge) =
      ∑ h : SurfaceHomology g,
        ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph with
            surfaceSubgraphHomology edgeClass F = h,
          surfaceParitySign
              (surfaceQuadraticParity lambda
                (surfaceSubgraphHomology edgeClass F)) *
            ∏ edge ∈ F, weight edge := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2]
    _ = _ := Finset.sum_fiberwise
      (G.edgeFinset.powerset.filter IsEvenSubgraph)
      (surfaceSubgraphHomology edgeClass)
      (fun F => surfaceParitySign
        (surfaceQuadraticParity lambda
          (surfaceSubgraphHomology edgeClass F)) *
        ∏ edge ∈ F, weight edge)

theorem surfaceQuadraticEvenPolynomial_real_eq_sectorRoot {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V → SurfaceHomology g)
    (weight : Sym2 V → Real) (lambda : SurfaceSpinStructure g) :
    surfaceQuadraticEvenPolynomial G edgeClass lambda
        (fun edge => (weight edge : Complex)) =
      (surfaceTwistedSectorRoot
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  rw [surfaceTwistedSectorRoot_graphSectorWeight]
  unfold surfaceQuadraticEvenPolynomial
  push_cast
  rfl



theorem surface_twisted_kacWard_det_eq_sectorSquare_of_base {g : Nat}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (edgeClass : Sym2 V → SurfaceHomology g)
    (hbase : ∀ w : Sym2 V → Complex,
      (1 - kwGraphTransition G w phase).det =
        surfaceQuadraticEvenPolynomial G edgeClass
          (0 : SurfaceSpinStructure g) w ^ 2)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V → Real) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda
        (fun edge => (weight edge : Complex))).det =
      (surfaceTwistedSectorSquare
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  rw [surface_twisted_kacWard_det_square_of_base G phase edgeClass hbase,
    surfaceQuadraticEvenPolynomial_real_eq_sectorRoot]
  simp [surfaceTwistedSectorSquare]

end
end StatMech.FrontierA
