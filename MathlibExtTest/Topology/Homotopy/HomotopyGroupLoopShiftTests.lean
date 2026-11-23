/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift

/-!
# Tests for the cube-based loop-space shift

These tests pin the equality-aware nonunital map, the one-cube
homeomorphism, the multiplicative loop-space shift, and its strict
naturality.  They exercise mixed universes and the first two degrees and
guard against exposing the proof-local flattening and reindexing machinery.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

universe u v w

namespace MathlibExtTest.Topology.Homotopy.HomotopyGroupLoopShiftTests

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- Equality-aware maps expose only multiplicativity. -/
example (f : C(X, Y)) (h : f x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x →ₙ*
      HomotopyGroup.Pi (n + 1) Y y :=
  HomotopyGroup.mapHomOfEq f h n

/-- The endpoint transport in the characteristic equation points from the
literal image basepoint to the chosen target basepoint. -/
example (f : C(X, Y)) (h : f x = y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f h n a =
      h ▸ HomotopyGroup.map f a :=
  HomotopyGroup.mapHomOfEq_apply f h n a

/-- The reverse endpoint transport does not inhabit the target group. -/
example (f : C(X, Y)) (_h : f x = y) (n : ℕ)
    (_a : HomotopyGroup.Pi (n + 1) X x) : True := by
  fail_if_success
    let P := fun y₀ => HomotopyGroup.Pi (n + 1) Y y₀
    let _bad : HomotopyGroup.Pi (n + 1) Y y :=
      Eq.mp (congrArg P _h.symm) (HomotopyGroup.map f _a)
  trivial

example (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq (ContinuousMap.id X) rfl n a = a :=
  HomotopyGroup.mapHomOfEq_id x n a

/-- Composition is source-first even when all endpoint equalities are
propositional inputs. -/
example (f : C(X, Y)) (g : C(Y, Z))
    (hf : f x = y) (hg : g y = z) (hfg : (g.comp f) x = z)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq (g.comp f) hfg n a =
      HomotopyGroup.mapHomOfEq g hg n
        (HomotopyGroup.mapHomOfEq f hf n a) :=
  HomotopyGroup.mapHomOfEq_comp f g hf hg hfg n a

/-- The one-cube comparison is a homeomorphism, not merely an equivalence. -/
example : GenLoop (Fin 1) X x ≃ₜ LoopSpace X x :=
  GenLoop.finOneHomeomorphLoopSpace X x

example :
    GenLoop.finOneHomeomorphLoopSpace X x
        (GenLoop.const : GenLoop (Fin 1) X x) =
      Path.refl x := by
  apply Path.ext
  rfl

example :
    (GenLoop.finOneHomeomorphLoopSpace X x).symm (Path.refl x) =
      (GenLoop.const : GenLoop (Fin 1) X x) := by
  apply GenLoop.ext
  intro t
  rfl

/-- The loop shift is universe-polymorphic and has the ordered degree shift
`(n + 1) ↦ (n + 2)`. -/
example (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x) ≃*
      HomotopyGroup.Pi (n + 2) X x :=
  HomotopyGroup.loopShiftMulEquiv n X x

/-- The first concrete shift starts with the fundamental group of the loop
space and lands in the second homotopy group. -/
example :
    HomotopyGroup.Pi 1 (LoopSpace X x) (Path.refl x) ≃*
      HomotopyGroup.Pi 2 X x :=
  HomotopyGroup.loopShiftMulEquiv 0 X x

example :
    HomotopyGroup.Pi 2 (LoopSpace X x) (Path.refl x) ≃*
      HomotopyGroup.Pi 3 X x :=
  HomotopyGroup.loopShiftMulEquiv 1 X x

/-- A universe-zero client. -/
example (X₀ : Type) [TopologicalSpace X₀] (x₀ : X₀) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X₀ x₀) (Path.refl x₀) ≃*
      HomotopyGroup.Pi (n + 2) X₀ x₀ :=
  HomotopyGroup.loopShiftMulEquiv n X₀ x₀

/-- A universe-one client. -/
example (X₁ : Type 1) [TopologicalSpace X₁] (x₁ : X₁) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X₁ x₁) (Path.refl x₁) ≃*
      HomotopyGroup.Pi (n + 2) X₁ x₁ :=
  HomotopyGroup.loopShiftMulEquiv n X₁ x₁

/-- Naturality uses strict loop postcomposition and the literal reflexive-loop
endpoint equality. -/
example (n : ℕ) (f : C(X, Y))
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y (f x)
        (HomotopyGroup.mapHomOfEq (ContinuousMap.strictLoopMap f x)
          (ContinuousMap.strictLoopMap_refl f x) n a) =
      HomotopyGroup.map f
        (HomotopyGroup.loopShiftMulEquiv n X x a) :=
  HomotopyGroup.loopShiftMulEquiv_naturality n f x a

/-- Identity compatibility follows from strict naturality. -/
example (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n X ((ContinuousMap.id X) x)
        (HomotopyGroup.mapHomOfEq
          (ContinuousMap.strictLoopMap (ContinuousMap.id X) x)
          (ContinuousMap.strictLoopMap_refl (ContinuousMap.id X) x) n a) =
      HomotopyGroup.map (ContinuousMap.id X)
        (HomotopyGroup.loopShiftMulEquiv n X x a) :=
  HomotopyGroup.loopShiftMulEquiv_naturality n
    (ContinuousMap.id X) x a

example (n : ℕ)
    (a : HomotopyGroup.Pi (n + 2) X x) :
    HomotopyGroup.map (ContinuousMap.id X) a = a :=
  HomotopyGroup.map_id a

/-- Source-first composition compatibility follows from naturality and the
source-first homotopy-group map calculus. -/
example (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Z ((g.comp f) x)
        (HomotopyGroup.mapHomOfEq
          (ContinuousMap.strictLoopMap (g.comp f) x)
          (ContinuousMap.strictLoopMap_refl (g.comp f) x) n a) =
      HomotopyGroup.map g
        (HomotopyGroup.map f
          (HomotopyGroup.loopShiftMulEquiv n X x a)) := by
  rw [HomotopyGroup.loopShiftMulEquiv_naturality]
  exact HomotopyGroup.map_comp f g _

/-- The source at `n = 0` carries the expected group structure. -/
example : Group
    (HomotopyGroup.Pi 1 (LoopSpace X x) (Path.refl x)) :=
  inferInstance

/-- The shifted target at `n = 0` carries the expected commutative group
structure. -/
example : CommGroup (HomotopyGroup.Pi 2 X x) :=
  inferInstance

#guard_msgs (error, substring := true) in
#check HomotopyGroup.finOneMapMulEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.flattenHomotopic

#guard_msgs (error, substring := true) in
#check HomotopyGroup.homotopyGroupFlattenEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.flatten_transAt

#guard_msgs (error, substring := true) in
#check HomotopyGroup.homotopyGroupFlattenMulEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.congrHomotopic

#guard_msgs (error, substring := true) in
#check HomotopyGroup.homotopyGroupCongrEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.congr_transAt

#guard_msgs (error, substring := true) in
#check HomotopyGroup.homotopyGroupCongrMulEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.loopShiftSingularEquiv

#guard_msgs (error, substring := true) in
#check HomotopyGroup.loopShiftWeakEquivalence

#guard_msgs (error, substring := true) in
#check HomotopyGroup.derivedLoopShiftMulEquiv

#print axioms HomotopyGroup.mapHomOfEq
#print axioms HomotopyGroup.mapHomOfEq_apply
#print axioms HomotopyGroup.mapHomOfEq_id
#print axioms HomotopyGroup.mapHomOfEq_comp
#print axioms GenLoop.finOneHomeomorphLoopSpace
#print axioms HomotopyGroup.loopShiftMulEquiv
#print axioms HomotopyGroup.loopShiftMulEquiv_naturality

end MathlibExtTest.Topology.Homotopy.HomotopyGroupLoopShiftTests
