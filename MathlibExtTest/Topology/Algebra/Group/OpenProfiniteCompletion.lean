/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Algebra.Group.OpenProfiniteCompletion

@[expose] public section

open ProfiniteGrp.OpenProfiniteCompletion

universe u

section GenericTop
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def topIndex : Index G :=
  ⟨FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup G), isOpen_univ⟩

example : FiniteGrp.{u} := (finiteGrpDiagram G).obj (topIndex G)

example : ProfiniteGrp.{u} := (diagram G).obj (topIndex G)

example : ProfiniteGrp.{u} := completion G

example (x : G) :
    ((etaFn G x).val (topIndex G) : G ⧸ (topIndex G).1.toSubgroup) =
    QuotientGroup.mk x :=
  etaFn_apply G x (topIndex G)

theorem continuous_eta_denseRange :
    Continuous (eta G) ∧ DenseRange (eta G) :=
  ⟨(eta G).continuous_toFun, denseRange_eta G⟩

end GenericTop

section FiniteDiscrete
variable (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [IsTopologicalGroup G]

example : Index G := topIndex G

example : FiniteGrp.{u} := (finiteGrpDiagram G).obj (topIndex G)

example : Continuous (eta G) ∧ DenseRange (eta G) :=
  continuous_eta_denseRange G

end FiniteDiscrete

section InfiniteDiscrete
-- Model case: `Multiplicative ℤ` with discrete topology; stated generically
-- so the corrected construction and density elaborate with no compactness.
variable (H : Type u) [Group H] [TopologicalSpace H] [DiscreteTopology H]
  [IsTopologicalGroup H] [Infinite H]

example : Index H := topIndex H

example : Infinite H := inferInstance

example : Continuous (eta H) ∧ DenseRange (eta H) :=
  continuous_eta_denseRange H

end InfiniteDiscrete
