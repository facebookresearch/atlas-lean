/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Filtered.NatTail
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CategoryTheory.Filtered.NatTail

#check @CategoryTheory.NatTail.tailFunctor
#print axioms CategoryTheory.NatTail.tailFunctor
#check @CategoryTheory.NatTail.tailFunctor_obj
#print axioms CategoryTheory.NatTail.tailFunctor_obj
#check @CategoryTheory.NatTail.tailFunctor_map
#print axioms CategoryTheory.NatTail.tailFunctor_map
#check @CategoryTheory.NatTail.tailFunctor_final
#print axioms CategoryTheory.NatTail.tailFunctor_final
#check @CategoryTheory.NatTail.typeTailCocone
#print axioms CategoryTheory.NatTail.typeTailCocone
#check @CategoryTheory.NatTail.typeTailIsColimit
#print axioms CategoryTheory.NatTail.typeTailIsColimit
#check @CategoryTheory.NatTail.typeTailIso
#print axioms CategoryTheory.NatTail.typeTailIso
#check @CategoryTheory.NatTail.typeTailIso_hom
#print axioms CategoryTheory.NatTail.typeTailIso_hom
#check @CategoryTheory.NatTail.typeTailIso_inv
#print axioms CategoryTheory.NatTail.typeTailIso_inv
#check @CategoryTheory.NatTail.typeTailIso_hom_ι
#print axioms CategoryTheory.NatTail.typeTailIso_hom_ι
#check @CategoryTheory.NatTail.typeTailIso_inv_ι
#print axioms CategoryTheory.NatTail.typeTailIso_inv_ι
#check @CategoryTheory.NatTail.typeTailIso_hom_naturality
#print axioms CategoryTheory.NatTail.typeTailIso_hom_naturality
#check @CategoryTheory.NatTail.typeTailIso_inv_naturality
#print axioms CategoryTheory.NatTail.typeTailIso_inv_naturality
#check @CategoryTheory.NatTail.typeTailDiagramFunctor
#print axioms CategoryTheory.NatTail.typeTailDiagramFunctor
#check @CategoryTheory.NatTail.typeTailColimitNatIso
#print axioms CategoryTheory.NatTail.typeTailColimitNatIso
#check @CategoryTheory.NatTail.typeTailColimitNatIso_app
#print axioms CategoryTheory.NatTail.typeTailColimitNatIso_app

section ActualTailMaps
open _root_.CategoryTheory.NatTail

/-- The actual index map is the original shifted order map at every offset. -/
example (r : ℕ) {i j : ℕ} (h : i ≤ j) :
    (tailFunctor r).map (homOfLE h) = homOfLE (Nat.add_le_add_left h r) :=
  tailFunctor_map r (homOfLE h)

/-- Every finite offset gives a genuinely final index functor. -/
example (r : ℕ) : (tailFunctor r).Final := tailFunctor_final r

/-- The actual whiskered cocone retains the complete selected colimit object. -/
example (D : ℕ ⥤ Type v) (r : ℕ) : (typeTailCocone D r).pt = colimit D := rfl

/-- Each forward function keeps the actual shifted colimit leg on every input. -/
example (D : ℕ ⥤ Type v) (r n : ℕ) (q : D.obj (r + n)) :
    (typeTailIso D r).hom (colimit.ι (tailFunctor r ⋙ D) n q) =
      colimit.ι D (r + n) q :=
  ConcreteCategory.congr_hom (typeTailIso_hom_ι D r n) q

/-- Each inverse function retains the same actual shifted source leg. -/
example (D : ℕ ⥤ Type v) (r n : ℕ) (q : D.obj (r + n)) :
    (typeTailIso D r).inv (colimit.ι D (r + n) q) =
      colimit.ι (tailFunctor r ⋙ D) n q :=
  ConcreteCategory.congr_hom (typeTailIso_inv_ι D r n) q

/-- Both complete tail-colimit functions retain the left inverse law. -/
example (D : ℕ ⥤ Type v) (r : ℕ) :
    (fun q => (typeTailIso D r).inv ((typeTailIso D r).hom q)) = id := by
  funext q
  exact ConcreteCategory.congr_hom (typeTailIso D r).hom_inv_id q

/-- Both complete tail-colimit functions retain the right inverse law. -/
example (D : ℕ ⥤ Type v) (r : ℕ) :
    (fun q => (typeTailIso D r).hom ((typeTailIso D r).inv q)) = id := by
  funext q
  exact ConcreteCategory.congr_hom (typeTailIso D r).inv_hom_id q

/-- The complete forward functions preserve every arbitrary diagram transformation. -/
example (r : ℕ) {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    (fun q => (typeTailIso E r).hom
      (colim.map (Functor.whiskerLeft (tailFunctor r) a) q)) =
    (fun q => colim.map a ((typeTailIso D r).hom q)) := by
  funext q
  exact ConcreteCategory.congr_hom (typeTailIso_hom_naturality r a) q

/-- The complete inverse functions preserve the same arbitrary input transformation. -/
example (r : ℕ) {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    (fun q => (typeTailIso E r).inv (colim.map a q)) =
    (fun q => colim.map (Functor.whiskerLeft (tailFunctor r) a)
      ((typeTailIso D r).inv q)) := by
  funext q
  exact ConcreteCategory.congr_hom (typeTailIso_inv_naturality r a) q

/-- The whole diagram functor retains the actual component map at the shifted index. -/
example (r n : ℕ) {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    ((typeTailDiagramFunctor r).map a).app n = a.app (r + n) := rfl

end ActualTailMaps

/-- All sixteen canonical roots retain actual kind, TYPE, safe VALUE and Std. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  (`CategoryTheory.NatTail.tailFunctor, "def"),
  (`CategoryTheory.NatTail.tailFunctor_obj, "theorem"),
  (`CategoryTheory.NatTail.tailFunctor_map, "theorem"),
  (`CategoryTheory.NatTail.tailFunctor_final, "theorem"),
  (`CategoryTheory.NatTail.typeTailCocone, "def"),
  (`CategoryTheory.NatTail.typeTailIsColimit, "def"),
  (`CategoryTheory.NatTail.typeTailIso, "def"),
  (`CategoryTheory.NatTail.typeTailIso_hom, "theorem"),
  (`CategoryTheory.NatTail.typeTailIso_inv, "theorem"),
  (`CategoryTheory.NatTail.typeTailIso_hom_ι, "theorem"),
  (`CategoryTheory.NatTail.typeTailIso_inv_ι, "theorem"),
  (`CategoryTheory.NatTail.typeTailIso_hom_naturality, "theorem"),
  (`CategoryTheory.NatTail.typeTailIso_inv_naturality, "theorem"),
  (`CategoryTheory.NatTail.typeTailDiagramFunctor, "def"),
  (`CategoryTheory.NatTail.typeTailColimitNatIso, "def"),
  (`CategoryTheory.NatTail.typeTailColimitNatIso_app, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  let modules : Array Lean.Name := #[
    `MathlibExt.CategoryTheory.Filtered.NatTail]
  for m in modules do
    let idx ← match env.getModuleIdx? m with
      | some i => pure i
      | none => throwError "Missing complete actual producer: {m}"
    let mut count : Nat := 0
    for (n, _) in env.constants do
      if env.getModuleIdxFor? n == some idx then
        count := count + 1
    unless count > 0 do
      throwError "Empty actual producer: {m}"
    Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count}"
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, expectedKind) in expectedKernelKinds do
    let m := `MathlibExt.CategoryTheory.Filtered.NatTail
    let idx ← match env.getModuleIdx? m with
      | some i => pure i
      | none => throwError "Missing actual producer module: {m}"
    let info ← match env.find? n with
      | some c => pure c
      | none => throwError "Missing complete actual root: {n}"
    let (kind, body) ← match info with
      | .defnInfo d =>
        unless d.safety == Lean.DefinitionSafety.safe do
          throwError "Unsafe actual whole VALUE: {n}"
        pure ("def", d.value)
      | .thmInfo d => pure ("theorem", d.value)
      | _ => throwError "Wrong actual kernel kind: {n}"
    unless kind == expectedKind do
      throwError "Wrong actual kernel kind: {n} {kind}"
    if info.type.hasMVar || info.type.hasLooseBVars then
      throwError "Incomplete actual whole TYPE: {n}"
    if body.hasMVar || body.hasLooseBVars then
      throwError "Incomplete actual whole VALUE: {n}"
    let actualIdx ← match env.getModuleIdxFor? n with
      | some i => pure i
      | none => throwError "Missing actual root module index: {n}"
    unless actualIdx == idx do
      throwError "Wrong actual root membership: {n}"
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless allowed.contains a do
        throwError "Nonstandard actual root: {n} {a}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
    Lean.logInfo m!"KERNEL_KIND_MODULE {m} {n} KIND {kind} NUMERIC_MODULE {actualIdx.toNat}"
    Lean.logInfo m!"ACTUAL_WHOLE_TYPE_VALUE_BOUND {m} {n}"
    Lean.logInfo m!"ACTUAL_STD_ROOT {m} {n} AXIOMS {axs}"
  Lean.logInfo m!"EXPECTED_ROOTS {expectedKernelKinds.size}"

#lint only unusedArguments in MathlibExt.CategoryTheory.Filtered.NatTail
#lint in MathlibExt.CategoryTheory.Filtered.NatTail

end MathlibExtTest.CategoryTheory.Filtered.NatTail
