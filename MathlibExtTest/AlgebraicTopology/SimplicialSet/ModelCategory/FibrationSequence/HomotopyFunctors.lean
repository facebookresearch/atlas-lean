/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors


import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory
open SSet.FibrationSequence.Geometry

namespace MathlibExtTest.FibrationSequenceCategoryWholeSourceCategory

/-- All public roots belong to the whole actual producer module. -/
def expectedProducerRootsCategory : Array Lean.Name := #[
  (`SSet.FibrationSequence.Geometry).append
    `hom_ext,
  (`SSet.FibrationSequence.Geometry).append
    `category,
  (`SSet.FibrationSequence.Geometry).append
    `totalFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `baseFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `fiberFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `totalFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `baseFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `fiberFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `projectionNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `inclusionNatTrans
]

#check @hom_ext
#print axioms hom_ext
#check @category
#print axioms category
#check @totalFunctor
#print axioms totalFunctor
#check @baseFunctor
#print axioms baseFunctor
#check @fiberFunctor
#print axioms fiberFunctor
#check @totalFunctor_map
#print axioms totalFunctor_map
#check @baseFunctor_map
#print axioms baseFunctor_map
#check @fiberFunctor_map
#print axioms fiberFunctor_map
#check @projectionNatTrans
#print axioms projectionNatTrans
#check @inclusionNatTrans
#print axioms inclusionNatTrans

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual whole Puppe producer"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for n in expectedProducerRootsCategory do
    unless (env.find? n).isSome do throwError "missing original source root: {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong actual source owner: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedProducerRootsCategory.size}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category
#lint in MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category

end MathlibExtTest.FibrationSequenceCategoryWholeSourceCategory




set_option autoImplicit false
noncomputable section
open CategoryTheory
open SSet.FibrationSequence.Geometry

namespace MathlibExtTest.FibrationSequencePiFunctorsWholeSourceHomotopy

/-- All public roots belong to the whole actual producer module. -/
def expectedProducerRootsHomotopy : Array Lean.Name := #[
  (`SSet.FibrationSequence.Geometry).append
    `totalPiFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `basePiFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `fiberPiFunctor,
  (`SSet.FibrationSequence.Geometry).append
    `totalPiFunctorOne,
  (`SSet.FibrationSequence.Geometry).append
    `basePiFunctorOne,
  (`SSet.FibrationSequence.Geometry).append
    `fiberPiFunctorOne,
  (`SSet.FibrationSequence.Geometry).append
    `totalPiFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `basePiFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `fiberPiFunctor_map,
  (`SSet.FibrationSequence.Geometry).append
    `projectionPiNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `inclusionPiNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `connectingPiNatTrans,
  (`SSet.FibrationSequence.Geometry).append
    `exact_at_base,
  (`SSet.FibrationSequence.Geometry).append
    `exact_at_fiber,
  (`SSet.FibrationSequence.Geometry).append
    `exact_at_total
]

#check @SSet.FibrationSequence.Geometry.totalPiFunctor
#print axioms SSet.FibrationSequence.Geometry.totalPiFunctor
#check @SSet.FibrationSequence.Geometry.basePiFunctor
#print axioms SSet.FibrationSequence.Geometry.basePiFunctor
#check @SSet.FibrationSequence.Geometry.fiberPiFunctor
#print axioms SSet.FibrationSequence.Geometry.fiberPiFunctor
#check @SSet.FibrationSequence.Geometry.totalPiFunctorOne
#print axioms SSet.FibrationSequence.Geometry.totalPiFunctorOne
#check @SSet.FibrationSequence.Geometry.basePiFunctorOne
#print axioms SSet.FibrationSequence.Geometry.basePiFunctorOne
#check @SSet.FibrationSequence.Geometry.fiberPiFunctorOne
#print axioms SSet.FibrationSequence.Geometry.fiberPiFunctorOne
#check @SSet.FibrationSequence.Geometry.totalPiFunctor_map
#print axioms SSet.FibrationSequence.Geometry.totalPiFunctor_map
#check @SSet.FibrationSequence.Geometry.basePiFunctor_map
#print axioms SSet.FibrationSequence.Geometry.basePiFunctor_map
#check @SSet.FibrationSequence.Geometry.fiberPiFunctor_map
#print axioms SSet.FibrationSequence.Geometry.fiberPiFunctor_map
#check @SSet.FibrationSequence.Geometry.projectionPiNatTrans
#print axioms SSet.FibrationSequence.Geometry.projectionPiNatTrans
#check @SSet.FibrationSequence.Geometry.inclusionPiNatTrans
#print axioms SSet.FibrationSequence.Geometry.inclusionPiNatTrans
#check @SSet.FibrationSequence.Geometry.connectingPiNatTrans
#print axioms SSet.FibrationSequence.Geometry.connectingPiNatTrans
#check @SSet.FibrationSequence.Geometry.exact_at_base
#print axioms SSet.FibrationSequence.Geometry.exact_at_base
#check @SSet.FibrationSequence.Geometry.exact_at_fiber
#print axioms SSet.FibrationSequence.Geometry.exact_at_fiber
#check @SSet.FibrationSequence.Geometry.exact_at_total
#print axioms SSet.FibrationSequence.Geometry.exact_at_total

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual whole Puppe producer"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for n in expectedProducerRootsHomotopy do
    unless (env.find? n).isSome do throwError "missing original source root: {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong actual source owner: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedProducerRootsHomotopy.size}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors
#lint in MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors

end MathlibExtTest.FibrationSequencePiFunctorsWholeSourceHomotopy

open scoped Simplicial

namespace MathlibExtTest.HomotopyGroupMapCanonicalSource

#check @SSet.KanComplex.π.map_congr
#print axioms SSet.KanComplex.π.map_congr
#check @SSet.KanComplex.π.map_square
#print axioms SSet.KanComplex.π.map_square

-- Map congruence is an equality of complete functions and needs no Kan or positive-degree premise.
example {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} {f g : X ⟶ Y}
    (hfg : f = g) (hf : f.app _ x = y) (hg : g.app _ x = y) (n : ℕ) :
    SSet.KanComplex.π.map f hf n = SSet.KanComplex.π.map g hg n :=
  SSet.KanComplex.π.map_congr hfg hf hg n

-- Different proofs of the same selected point equation do not change the degree-zero map.
example {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y)
    (h₁ h₂ : f.app _ x = y) :
    SSet.KanComplex.π.map f h₁ 0 = SSet.KanComplex.π.map f h₂ 0 :=
  SSet.KanComplex.π.map_congr rfl h₁ h₂ 0

-- A genuine source-first simplicial square induces the square in each literal degree.
example {X Y Z W : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    {z : Z _⦋0⦌} {w : W _⦋0⦌}
    (f : X ⟶ Y) (g : Z ⟶ W) (a : X ⟶ Z) (b : Y ⟶ W)
    (h : a ≫ g = f ≫ b) (hf : f.app _ x = y) (hg : g.app _ z = w)
    (ha : a.app _ x = z) (hb : b.app _ y = w) (n : ℕ)
    (q : SSet.KanComplex.π n X x) :
    SSet.KanComplex.π.map g hg n (SSet.KanComplex.π.map a ha n q) =
      SSet.KanComplex.π.map b hb n (SSet.KanComplex.π.map f hf n q) :=
  SSet.KanComplex.π.map_square f g a b h hf hg ha hb n q

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
  let some idx := env.getModuleIdx? m | throwError "missing canonical homotopy-map producer"
  for n in #[`SSet.KanComplex.π.map_congr, `SSet.KanComplex.π.map_square] do
    unless env.getModuleIdxFor? n == some idx do
      throwError "wrong canonical homotopy-map owner: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
#lint in MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

end MathlibExtTest.HomotopyGroupMapCanonicalSource
