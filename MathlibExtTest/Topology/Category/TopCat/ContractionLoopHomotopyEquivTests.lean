/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ContractionLoopHomotopyEquiv

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped Topology.Homotopy

universe u

namespace TopCat.ContractionLoopHomotopyEquivTests

variable {E B : TopCat.{u}} (p : E ⟶ B) (b : B) (e : E)

example : Type u := pointFiber p b

private def exactTwoFields (H : BasedContraction E e) :
    BasedContraction E e :=
  match H with
  | ⟨homotopy, fixed⟩ =>
      { homotopy := homotopy
        fixed := fixed }

section Positive

variable (he : p e = b) (H : BasedContraction E e)
variable (L : PathLiftingData p)

example : TopCat.of (pointFiber p b) ⟶ TopCat.of (LoopSpace B b) :=
  contractionLoopMap p b e he H

example (x : pointFiber p b) (t : unitInterval) :
    contractionLoopMap p b e he H x t =
      p (H.homotopy (t, x.1)) :=
  contractionLoopMap_apply p b e he H x t

example (x : pointFiber p b) :
    contractionLoopMap p b e he H x 0 = b :=
  (contractionLoopMap p b e he H x).source

example (x : pointFiber p b) :
    contractionLoopMap p b e he H x 1 = b :=
  (contractionLoopMap p b e he H x).target

example :
    contractionLoopMap p b e he H ⟨e, he⟩ = Path.refl b :=
  contractionLoopMap_basepoint p b e he H

example :
    ContinuousMap.HomotopyEquiv (pointFiber p b) (LoopSpace B b) :=
  contractionLoopHomotopyEquiv p b e he H L

example :
    (contractionLoopHomotopyEquiv p b e he H L).toFun =
      (contractionLoopMap p b e he H).hom := by
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  rw [contractionLoopHomotopyEquiv_apply, contractionLoopMap_apply]

example (x : pointFiber p b) (t : unitInterval) :
    contractionLoopHomotopyEquiv p b e he H L x t =
      p (H.homotopy (t, x.1)) :=
  contractionLoopHomotopyEquiv_apply p b e he H L x t

example :
    ((contractionLoopHomotopyEquiv p b e he H L).invFun.comp
      (contractionLoopHomotopyEquiv p b e he H L).toFun).Homotopic
        (ContinuousMap.id (pointFiber p b)) :=
  (contractionLoopHomotopyEquiv p b e he H L).left_inv

example :
    ((contractionLoopHomotopyEquiv p b e he H L).toFun.comp
      (contractionLoopHomotopyEquiv p b e he H L).invFun).Homotopic
        (ContinuousMap.id (LoopSpace B b)) :=
  (contractionLoopHomotopyEquiv p b e he H L).right_inv

end Positive

-- Path-lifting data cannot be omitted.
example (_he : p e = b) (_H : BasedContraction E e) : True := by
  fail_if_success
    have _ : ContinuousMap.HomotopyEquiv
        (pointFiber p b) (LoopSpace B b) :=
      contractionLoopHomotopyEquiv p b e _he _H
  trivial

-- The equation placing the contraction point over the loop basepoint cannot
-- be omitted.
example (_H : BasedContraction E e) (_L : PathLiftingData p) : True := by
  fail_if_success
    have _ : ContinuousMap.HomotopyEquiv
        (pointFiber p b) (LoopSpace B b) :=
      contractionLoopHomotopyEquiv p b e _H _L
  trivial

-- A contraction cannot be omitted in favor of path-lifting data alone.
example (_he : p e = b) (_L : PathLiftingData p) : True := by
  fail_if_success
    have _ : ContinuousMap.HomotopyEquiv
        (pointFiber p b) (LoopSpace B b) :=
      contractionLoopHomotopyEquiv p b e _he _L
  trivial

-- Fixedness of the chosen endpoint is a separate load-bearing field.
example (_K : ContinuousMap.Homotopy
    (ContinuousMap.id E) (ContinuousMap.const E e)) : True := by
  fail_if_success
    have _ : BasedContraction E e :=
      { homotopy := _K }
  trivial

-- Path-lifting data stay explicit rather than becoming a global instance.
example : True := by
  fail_if_success
    let _ : PathLiftingData p := inferInstance
  trivial

-- Proof machinery and later consumer conclusions are intentionally private
-- or absent from the provider.
example (_L : PathLiftingData p) : True := by
  fail_if_success
    have _ := _L.universalReversedLoopLift
  fail_if_success
    have _ := _L.fiberDeformationEndpoint
  fail_if_success
    have _ := TopCat.contractionLoopInverse
  fail_if_success
    have _ := TopCat.contractionLoopStrictFiberEquiv
  fail_if_success
    have _ := TopCat.contractionLoopWeakEquivalence
  fail_if_success
    have _ := TopCat.contractionLoopFibration
  fail_if_success
    have _ := TopCat.contractionLoopBar
  fail_if_success
    have _ := TopCat.contractionLoopEG
  fail_if_success
    have _ := TopCat.contractionLoopBG
  trivial

section UniverseOne

variable {E₁ B₁ : TopCat.{1}} (p₁ : E₁ ⟶ B₁)
variable (b₁ : B₁) (e₁ : E₁) (he₁ : p₁ e₁ = b₁)
variable (H₁ : BasedContraction E₁ e₁) (L₁ : PathLiftingData p₁)

example :
    ContinuousMap.HomotopyEquiv (pointFiber p₁ b₁) (LoopSpace B₁ b₁) :=
  contractionLoopHomotopyEquiv p₁ b₁ e₁ he₁ H₁ L₁

end UniverseOne

section UniverseZero

variable {E₀ B₀ : TopCat.{0}} (p₀ : E₀ ⟶ B₀)
variable (b₀ : B₀) (e₀ : E₀) (he₀ : p₀ e₀ = b₀)
variable (H₀ : BasedContraction E₀ e₀) (L₀ : PathLiftingData p₀)

example :
    ContinuousMap.HomotopyEquiv (pointFiber p₀ b₀) (LoopSpace B₀ b₀) :=
  contractionLoopHomotopyEquiv p₀ b₀ e₀ he₀ H₀ L₀

end UniverseZero

end TopCat.ContractionLoopHomotopyEquivTests

#check TopCat.BasedContraction
#check TopCat.pointFiber
#check TopCat.contractionLoopMap
#check TopCat.contractionLoopMap_apply
#check TopCat.contractionLoopMap_basepoint
#check TopCat.contractionLoopHomotopyEquiv
#check TopCat.contractionLoopHomotopyEquiv_apply

#print axioms TopCat.BasedContraction
#print axioms TopCat.pointFiber
#print axioms TopCat.contractionLoopMap
#print axioms TopCat.contractionLoopMap_apply
#print axioms TopCat.contractionLoopMap_basepoint
#print axioms TopCat.contractionLoopHomotopyEquiv
#print axioms TopCat.contractionLoopHomotopyEquiv_apply

end
