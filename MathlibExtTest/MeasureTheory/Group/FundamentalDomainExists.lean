/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Group.FundamentalDomainExists

@[expose] public section

example (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : DiscreteTopology Γ) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x : G, ∃! γ : Γ, x * (γ : G) ∈ D) ∧
      ∀ μ : MeasureTheory.Measure G, MeasureTheory.IsFundamentalDomain Γ.op D μ :=
  MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology Γ hΓ
