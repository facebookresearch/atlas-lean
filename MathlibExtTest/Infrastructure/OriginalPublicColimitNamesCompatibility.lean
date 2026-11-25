/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lean
import MathlibExt.CategoryTheory.Adjunction.SourceHomColimit
import MathlibExt.CategoryTheory.SmallObject.AdjointFamilySourceSmallness
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite

run_cmd do
  let env ← Lean.getEnv
  let names : Array (Lean.Name × Lean.Name) := #[
    (`CategoryTheory.Adjunction.isColimit_leftAdjointSource,
      `CategoryTheory.Adjunction.isColimitLeftAdjointSource),
    (`HomotopicalAlgebra.adjointFamilySource_mappedCanonicalCocone,
      `HomotopicalAlgebra.adjointFamilySourceMappedCanonicalCocone),
    (`CategoryTheory.TransfiniteCompositionOfShape.map_cgwhToCompactlyGenerated_of_injective,
      `CategoryTheory.TransfiniteCompositionOfShape.mapCgwhToCompactlyGeneratedOfInjective)]
  for (oldName, canonicalName) in names do
    let old ← Lean.getConstInfo oldName
    let canonical ← Lean.getConstInfo canonicalName
    unless old.levelParams == canonical.levelParams do
      throwError "Original full universe parameters changed: {oldName}"
    let .ok true := Lean.Kernel.isDefEq env {} old.type canonical.type |
      throwError "Original full TYPE changed: {oldName}"
    let some oldBody := old.value? (allowOpaque := true) |
      throwError "Original mathematical DATA body missing: {oldName}"
    let canonicalValue := Lean.mkConst canonicalName (old.levelParams.map Lean.Level.param)
    let .ok true := Lean.Kernel.isDefEq env {} oldBody canonicalValue |
      throwError "Original complete DATA changed: {oldName}"
    let axioms ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms oldName
    unless axioms.all #[`propext, `Classical.choice, `Quot.sound].contains do
      throwError "Original API uses unsupported axioms: {oldName}"
    Lean.logInfo m!"Original public TYPE, complete DATA and universe positions preserved: {oldName}"
