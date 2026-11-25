/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.MumfordPeriod

@[expose] public section

open Mumford

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

/-- The quotient degeneracy data of a graph with a graph action has the
expected vertex maps on representatives. -/
example {G W : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] [∀ d : 𝒯.Dart, Finite (MulAction.stabilizer G d)]
    (d : 𝒯.Dart) :
    (quotientDegeneracyData G 𝒯).a (Quotient.mk'' d) = Quotient.mk'' d.fst ∧
      (quotientDegeneracyData G 𝒯).b (Quotient.mk'' d) =
        Quotient.mk'' d.snd :=
  ⟨rfl, rfl⟩

/-- Every group action preserves adjacency in a complete graph. -/
local instance {G W : Type} [Group G] [MulAction G W] :
    GraphAction G (⊤ : SimpleGraph W) :=
  ⟨fun g v w h => by
    rw [SimpleGraph.top_adj] at h ⊢
    exact (MulAction.injective g).ne h⟩

/-- A trivial group has trivial dart stabilizers, so every quotient edge has
width `1`. -/
example {G W : Type} [Group G] [Subsingleton G] [MulAction G W]
    (𝒯 : SimpleGraph W) [GraphAction G 𝒯] (e : QuotEdge G 𝒯) :
    stabWidth G 𝒯 e = 1 := by
  apply PNat.eq
  show Nat.card (MulAction.stabilizer G e.out) = 1
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Conjugation by the abelian group of order `2` is a trivial action on the
complete graph on its two elements, so the stabilizer of each dart is the whole
group and the width of the quotient edge is `2`. -/
example (d : (⊤ : SimpleGraph (Multiplicative (ZMod 2))).Dart) :
    stabWidth (ConjAct (Multiplicative (ZMod 2))) ⊤ (Quotient.mk'' d) = 2 := by
  have htop :
      MulAction.stabilizer (ConjAct (Multiplicative (ZMod 2))) d = ⊤ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
    refine SimpleGraph.Dart.ext _ _ (Prod.ext ?_ ?_) <;>
      simp [ConjAct.smul_def, mul_inv_cancel_comm]
  rw [stabWidth_mk]
  apply PNat.eq
  show Nat.card (MulAction.stabilizer (ConjAct (Multiplicative (ZMod 2))) d) = 2
  rw [htop, Subgroup.card_top,
    Nat.card_congr (ConjAct.ofConjAct.toEquiv.trans Multiplicative.toAdd),
    Nat.card_zmod]

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
