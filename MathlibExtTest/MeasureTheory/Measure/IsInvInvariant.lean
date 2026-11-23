/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.IsInvInvariant

@[expose] public section

open MeasureTheory

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant :=
  MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant μ
