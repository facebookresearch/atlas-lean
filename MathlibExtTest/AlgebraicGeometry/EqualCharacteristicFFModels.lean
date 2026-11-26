/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EqualCharacteristicFFModels

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.EqualCharacteristicFFModels

open MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
open WantedExt.AlgebraicGeometry.EqualCharacteristicFFModels

/-- The Laurent-series field over `ZMod p` is a nonarchimedean local field. -/
example (p : ℕ) [Fact p.Prime] :
    letI := valuativeRelation (ZMod p)
    IsNonarchimedeanLocalField (CoefficientField (ZMod p)) :=
  laurentSeriesLocalField p (ZMod p)

/-- The Laurent-series field over `ZMod p` is locally compact. -/
example (p : ℕ) [Fact p.Prime] : LocallyCompactSpace (CoefficientField (ZMod p)) :=
  letI := valuativeRelation (ZMod p)
  haveI : IsNonarchimedeanLocalField (CoefficientField (ZMod p)) :=
    laurentSeriesLocalField p (ZMod p)
  inferInstance

end MathlibExtTest.AlgebraicGeometry.EqualCharacteristicFFModels
