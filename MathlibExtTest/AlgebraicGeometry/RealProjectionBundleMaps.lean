/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RealProjectionBundleMaps

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata
open MathlibExt.AlgebraicGeometry.RealProjectionBundleMaps
open Bundle

namespace MathlibExtTest.AlgebraicGeometry.RealProjectionBundleMaps

variable {n r : ℕ} {X : RealVariety n}

/-- The trivial bundle of rank `r`: the identity projection. -/
def trivialBundle (X : RealVariety n) (r : ℕ) : ProjectionBundle X r where
  projection _ := 1
  continuous := continuous_const
  idempotent _ := by simp
  symmetric _ := by simp

-- Its fibres are the whole space, and the bounded operators are the identity.
example (x : X.locus) : (trivialBundle X r).fiber x = ⊤ := by
  simp [ProjectionBundle.fiber, trivialBundle]

example (x : X.locus) : operator (trivialBundle X r) x = 1 := by
  ext v i
  simp [operator, matrixOperator, trivialBundle]

/-- The model fibre `ℝ^r` is the fibre of the trivial bundle everywhere. -/
def trivialFibreEquiv (x : X.locus) :
    Vectors r ≃L[ℝ] (operator (trivialBundle X r) x).range :=
  (LinearEquiv.ofTop _ (by
    rw [operator_range]
    simp [ProjectionBundle.fiber, trivialBundle])).symm.toContinuousLinearEquiv

-- The native fibre bundle and vector bundle structures can be instantiated.
example : FiberBundle (Vectors r) (fun x : X.locus ↦ (operator (trivialBundle X r) x).range) :=
  nativeFiberBundle (trivialBundle X r) (Vectors r) fun x ↦ ⟨trivialFibreEquiv x⟩

example :
    letI := nativeFiberBundle (trivialBundle X r) (Vectors r) fun x ↦ ⟨trivialFibreEquiv x⟩
    VectorBundle ℝ (Vectors r) (fun x : X.locus ↦ (operator (trivialBundle X r) x).range) :=
  nativeVectorBundle (trivialBundle X r) (Vectors r) fun x ↦ ⟨trivialFibreEquiv x⟩

-- Every projection family has a local bundle on the neighbourhood of each point.
example (P : ProjectionBundle X r) (x : X.locus) : x ∈ trivializingOpen P x :=
  mem_trivializingOpen P x

example (P : ProjectionBundle X r) (x : X.locus) :
    letI := localFiberBundle P x
    VectorBundle ℝ (operator P x).range
      (fun y : trivializingOpen P x ↦ (operator P y.val).range) :=
  localVectorBundle P x

-- The classifying map records the projection itself, so its range is the fibre.
example (P : ProjectionBundle X r) (x : X.locus) :
    (classifying P x).val = P.projection x :=
  rfl

example (P : ProjectionBundle X r) (x : X.locus) :
    LinearMap.range (Matrix.toLin' (classifying P x).val) = P.fiber x :=
  classifying_fiber P x

-- Pulling back composes the classifying map and keeps the fibres.
example {m : ℕ} (P : ProjectionBundle X r) (Y : RealVariety m) (f : Y.locus → X.locus)
    (hf : Continuous f) (y : Y.locus) :
    classifying (pullback P Y f hf) y = classifying P (f y) :=
  congrFun (pullback_classifying P Y f hf) y

example {m : ℕ} (P : ProjectionBundle X r) (Y : RealVariety m) (f : Y.locus → X.locus)
    (hf : Continuous f) (y : Y.locus) :
    (pullback P Y f hf).fiber y = P.fiber (f y) :=
  pullback_fiber P Y f hf y

-- Pulling back along the identity changes nothing.
example (P : ProjectionBundle X r) :
    (pullback P X id continuous_id).projection = P.projection :=
  rfl

/-! ### Regular maps -/

/-- The identity regular map. -/
def regularId (X : RealVariety n) : RegularMap X X where
  map := id
  regular i f hf x _ := ⟨MvPolynomial.X i, 1, by simp, fun y hy _ ↦ by
    simpa using hf ⟨y, hy⟩⟩
  map_continuous := continuous_id

-- A regular map is determined by its map of real points: no data off the source locus.
example {m : ℕ} {Y : RealVariety m} (f g : RegularMap X Y) (h : ∀ x, f.map x = g.map x) :
    f = g :=
  RegularMap.ext (funext h)

/-- The empty variety in the real line: the zeros of `0` minus the zeros of `0`. -/
def emptyVariety : RealVariety 1 := ⟨⊥, ⊥⟩

-- In particular on the empty variety there is exactly one regular endomorphism.
example (f g : RegularMap emptyVariety emptyVariety) : f = g := by
  have hempty : IsEmpty emptyVariety.locus :=
    ⟨fun x ↦ x.property.2 (by simp [emptyVariety])⟩
  exact RegularMap.ext (funext fun x ↦ hempty.elim x)

-- Pulling back along the identity regular map changes nothing.
example (P : ProjectionBundle X r) :
    (regularPullback P X (regularId X)).projection = P.projection :=
  rfl

-- Algebraicity of a bundle on a set is regularity of its classifying map there.
example (P : ProjectionBundle X r) (S : Set (Ambient n)) :
    classifyingRegularOn P S ↔ IsAlgebraicOn P S :=
  classifyingRegularOn_iff P S

end MathlibExtTest.AlgebraicGeometry.RealProjectionBundleMaps
