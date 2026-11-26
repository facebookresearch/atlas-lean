/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.MumfordPeriod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

open Mumford CerednikDrinfeld CerednikDrinfeld.Mumford

namespace MumfordPeriodTest

/-- Consumer with the original binders: the ribbon kernel is characterized
by vanishing under both degeneracy maps. -/
example {E V : Type*} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 :=
  mem_ribbonKernel

/-- Nontrivial instance: one edge with distinct ends and width `2`. The
zero chain lies in the ribbon kernel, the Gram pairing is symmetric on it,
and the period datum built from the zero pairing with the zero valuation
satisfies its defining equations. -/
example : True := by
  let D : DegeneracyData (Fin 1) (Fin 2) :=
    { a := fun _ => 0, b := fun _ => 1, w := fun _ => 2 }
  have h0 : (0 : Fin 1 → ℤ) ∈ ribbonKernel D := by
    rw [mem_ribbonKernel]
    intro i
    simp [jointDelta, pushforward]
  let P : PeriodDatum D ℚ ℚ (0 : Additive ℚˣ →+ ℤ) :=
    { Q := 0
      Q_symm := fun x y => rfl
      ord_Q := fun x y => by
        have hx : x.1 0 = 0 := by
          have h := mem_ribbonKernel.mp x.2 0
          have hDa : D.a 0 = 0 := rfl
          simpa [jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
            dotProduct, Fin.sum_univ_one, hDa] using congrFun h 0
        simp [ribbonGram_apply, hx] }
  have hsymm : ∀ x y : ribbonKernel D, P.Q x y = P.Q y x := P.Q_symm
  trivial

/-- Two parallel edges from `0` to `1`, with widths `1` and `2`. -/
private def twoEdges : DegeneracyData (Fin 2) (Fin 2) where
  a _ := 0
  b _ := 1
  w := ![1, 2]

/-- The difference of the two edges lies in the ribbon kernel. -/
private theorem diff_mem_ribbonKernel :
    (![1, -1] : Fin 2 → ℤ) ∈ ribbonKernel twoEdges := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  fin_cases i <;> fin_cases v <;>
    simp [twoEdges, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The difference of the two edges, as an element of the ribbon kernel. -/
private def diff : ribbonKernel twoEdges := ⟨_, diff_mem_ribbonKernel⟩

/-- The `2`-adic valuation on the units of `ℚ`. -/
private noncomputable def ord₂ : Additive ℚˣ →+ ℤ :=
  AddMonoidHom.mk' (fun u => padicValRat 2 ((Additive.toMul u : ℚˣ) : ℚ))
    fun u v => by
      simp [padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]

/-- The unit `2` of `ℚ`. -/
private def two : ℚˣ := Units.mk0 2 two_ne_zero

private theorem ord₂_two : ord₂ (Additive.ofMul two) = 1 := by
  show padicValRat 2 ((two : ℚˣ) : ℚ) = 1
  rw [two, Units.val_mk0]
  exact_mod_cast padicValRat.self (p := 2) one_lt_two

/-- The period datum `Q x y = 2 ^ ⟨x, y⟩` on the two parallel edges, for the
`2`-adic valuation. -/
private noncomputable def twoEdgesPeriod : PeriodDatum twoEdges ℚ ℚ ord₂ where
  Q := (ribbonGram twoEdges).compr₂
    (LinearMap.toSpanSingleton ℤ (Additive ℚˣ) (Additive.ofMul two))
  Q_symm x y := by
    simp only [LinearMap.compr₂_apply, ribbonGram_apply]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  ord_Q x y := by
    rw [LinearMap.compr₂_apply, LinearMap.toSpanSingleton_apply, map_zsmul,
      ord₂_two, smul_eq_mul, mul_one]

/-- A period datum with a nonzero Gram value. On two parallel edges of widths
`1` and `2`, the difference of the edges lies in the ribbon kernel, its Gram
value is `1 + 2 = 3`, and the valuation of its period is `3`. -/
example : ribbonGram twoEdges diff diff = 3 ∧
    ord₂ (twoEdgesPeriod.Q diff diff) = 3 := by
  have h : ribbonGram twoEdges diff diff = 3 := by
    rw [ribbonGram_apply, Fin.sum_univ_two]
    norm_num [diff, twoEdges]
  exact ⟨h, (twoEdgesPeriod.ord_Q diff diff).trans h⟩

/-- The trivial action of the trivial group on `Fin 3`. -/
local instance : MulAction Unit (Fin 3) where
  smul _ w := w
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance : GraphAction Unit (SimpleGraph.pathGraph 3) :=
  ⟨fun _ _ _ h => h⟩

/-- The dart `0 → 1` of the path `0 - 1 - 2`. -/
private def d₀₁ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(0, 1), by simp [SimpleGraph.pathGraph_adj]⟩

/-- The dart `1 → 0` of the path `0 - 1 - 2`. -/
private def d₁₀ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(1, 0), by simp [SimpleGraph.pathGraph_adj]⟩

/-- The dart `1 → 2` of the path `0 - 1 - 2`. -/
private def d₁₂ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(1, 2), by simp [SimpleGraph.pathGraph_adj]⟩

private theorem eq_of_mk_vert_eq {v w : Fin 3}
    (h : (Quotient.mk'' v : QuotVert Unit (Fin 3)) = Quotient.mk'' w) :
    v = w := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨_, hg⟩ := h
  exact hg.symm

private theorem eq_of_mk_dart_eq {d d' : (SimpleGraph.pathGraph 3).Dart}
    (h : (Quotient.mk'' d : QuotEdge Unit (SimpleGraph.pathGraph 3)) =
      Quotient.mk'' d') :
    d = d' := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨_, hg⟩ := h
  exact hg.symm

/-- `formalU` is not symmetric. Under the trivial action on the path
`0 - 1 - 2`, the dart `0 → 1` continues by `1 → 2`, so the entry at
`(0 → 1, 1 → 2)` is `1`, while `1 → 2` does not continue by `0 → 1`, so the
entry at `(1 → 2, 0 → 1)` is `0`. The entry at `(0 → 1, 1 → 0)` is `0` too,
because `formalU` does not backtrack. -/
example [Fintype (QuotEdge Unit (SimpleGraph.pathGraph 3))]
    [DecidableEq (QuotEdge Unit (SimpleGraph.pathGraph 3))]
    [Fintype (QuotVert Unit (Fin 3))] [DecidableEq (QuotVert Unit (Fin 3))] :
    formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₀₁) (Quotient.mk'' d₁₂) = 1 ∧
      formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₁₂) (Quotient.mk'' d₀₁) = 0 ∧
      formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₀₁) (Quotient.mk'' d₁₀) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [formalU_apply, ite_eq_left]
    refine ⟨rfl, fun h => ?_⟩
    have h20 : (2 : Fin 3) = 0 :=
      congrArg (fun d : (SimpleGraph.pathGraph 3).Dart => d.fst)
        (eq_of_mk_dart_eq h)
    exact absurd h20 (by decide)
  · rw [formalU_apply, ite_eq_right]
    rintro ⟨h, -⟩
    exact absurd (eq_of_mk_vert_eq (v := 2) (w := 0) h) (by decide)
  · rw [formalU_apply, ite_eq_right]
    rintro ⟨-, h⟩
    exact h rfl

/-- `U` is the preimage of the torsion of the Jacobian, so it contains the
period lattice. -/
example {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) : P.periodLattice ≤ P.U := by
  intro x hx
  show P.periodLattice.mkQ x ∈ Submodule.torsion ℤ P.JacPoints
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact zero_mem _

/-- Base change of units is the identity on `ℚ`. -/
example (u : ℚˣ) :
    unitsBaseChange ℚ ℚ (Additive.ofMul u) = Additive.ofMul u := by
  simp

end MumfordPeriodTest
