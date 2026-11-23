/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

#check TopCat.loopPathObjectMap
#print axioms TopCat.loopPathObjectMap
#check TopCat.loopPathObjectMap_evalZero
#print axioms TopCat.loopPathObjectMap_evalZero
#check TopCat.loopPathObjectMap_evalOne
#print axioms TopCat.loopPathObjectMap_evalOne
#check TopCat.loopConstantHomotopyFiber
#print axioms TopCat.loopConstantHomotopyFiber
#check TopCat.loopConstantHomotopyFiber_path
#print axioms TopCat.loopConstantHomotopyFiber_path
#check TopCat.loopConstantHomotopyFiber_toTotal
#print axioms TopCat.loopConstantHomotopyFiber_toTotal
#check TopCat.loopHomotopyFiberConstIso
#print axioms TopCat.loopHomotopyFiberConstIso
#check TopCat.loopToHomotopyFiber
#print axioms TopCat.loopToHomotopyFiber
#check TopCat.loopToHomotopyFiber_toTotal
#print axioms TopCat.loopToHomotopyFiber_toTotal
#check TopCat.loopToHomotopyFiber_path
#print axioms TopCat.loopToHomotopyFiber_path
#check TopCat.loopToHomotopyFiber_mem_of_total_conull
#print axioms TopCat.loopToHomotopyFiber_mem_of_total_conull
#check TopCat.homotopyFiberSelectedPointMap
#print axioms TopCat.homotopyFiberSelectedPointMap
#check TopCat.homotopyFiberSelectedPointMap_toTotal
#print axioms TopCat.homotopyFiberSelectedPointMap_toTotal
#check TopCat.homotopyFiberSelectedPointMap_path
#print axioms TopCat.homotopyFiberSelectedPointMap_path
#check TopCat.loopToHomotopyFiber_constant_point
#print axioms TopCat.loopToHomotopyFiber_constant_point

-- Both inverse identities hold on the complete original raw spaces.
example (B : TopCat.{u}) (b : B) :
    (TopCat.loopHomotopyFiberConstIso B b).hom ≫
        (TopCat.loopHomotopyFiberConstIso B b).inv =
      𝟙 (TopCat.of (LoopSpace B b)) :=
  (TopCat.loopHomotopyFiberConstIso B b).hom_inv_id

example (B : TopCat.{u}) (b : B) :
    (TopCat.loopHomotopyFiberConstIso B b).inv ≫
        (TopCat.loopHomotopyFiberConstIso B b).hom =
      𝟙 (TopCat.homotopyFiber
        (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) b) :=
  (TopCat.loopHomotopyFiberConstIso B b).inv_hom_id

section SelectedLoop

variable {E B : TopCat.{u}} (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b)

example (hE : TopCat.weakHomotopyEquivalences (terminal.from E)) :
    TopCat.weakHomotopyEquivalences (TopCat.loopToHomotopyFiber p e0 b he) :=
  TopCat.loopToHomotopyFiber_mem_of_total_conull p e0 b he hE

example :
    TopCat.loopToHomotopyFiber p e0 b he ≫ TopCat.homotopyFiberToTotal p b =
      TopCat.const e0 := TopCat.loopToHomotopyFiber_toTotal p e0 b he

example :
    TopCat.loopToHomotopyFiber p e0 b he ≫ TopCat.homotopyFiberPath p b =
      TopCat.loopPathObjectMap B b := TopCat.loopToHomotopyFiber_path p e0 b he

example (gamma : LoopSpace B b) (t : TopCat.I.{u}) :
    TopCat.homotopyFiberPath p b (TopCat.loopToHomotopyFiber p e0 b he gamma) t =
      gamma (TopCat.I.homeomorph t) := by
  have h := ConcreteCategory.congr_hom
    (TopCat.loopToHomotopyFiber_path p e0 b he) gamma
  exact congrArg (fun q : TopCat.pathObject B => q t) h

-- The joint loop/parameter family uses the actual selected-loop map.
example : Continuous (fun z : LoopSpace B b × TopCat.I.{u} =>
    TopCat.homotopyFiberPath p b (TopCat.loopToHomotopyFiber p e0 b he z.1) z.2) :=
  continuous_eval.comp
    (((TopCat.homotopyFiberPath p b).hom.continuous.comp
      ((TopCat.loopToHomotopyFiber p e0 b he).hom.continuous.comp continuous_fst)).prodMk
      continuous_snd)

-- The point is independently selected by the strict-fiber constant-path comparison.
example :
    (TopCat.const (Path.refl b) : TopCat.of PUnit.{u + 1} ⟶
        TopCat.of (LoopSpace B b)) ≫ TopCat.loopToHomotopyFiber p e0 b he =
      TopCat.homotopyFiberSelectedPointMap p e0 b he :=
  TopCat.loopToHomotopyFiber_constant_point p e0 b he

example :
    TopCat.homotopyFiberSelectedPointMap p e0 b he ≫ TopCat.homotopyFiberToTotal p b =
      TopCat.const e0 := TopCat.homotopyFiberSelectedPointMap_toTotal p e0 b he

example :
    TopCat.homotopyFiberSelectedPointMap p e0 b he ≫ TopCat.homotopyFiberPath p b =
      TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1})
        (ContinuousMap.const TopCat.I.{u} b)) :=
  TopCat.homotopyFiberSelectedPointMap_path p e0 b he

end SelectedLoop
