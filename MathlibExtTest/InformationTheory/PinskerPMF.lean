/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.PinskerPMF

/-- Boundary check: Pinsker's inequality instantiates on a
two-point space. -/
example (p q : PMF (Fin 2)) :
    ENNReal.ofReal ((∑ a, |(p a).toReal - (q a).toReal|) ^ 2) ≤
      2 * InformationTheory.klDiv p.toMeasure q.toMeasure :=
  pinsker_pmf p q
