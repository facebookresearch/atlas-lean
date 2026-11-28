/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata
public import MathlibExt.Topology.VectorBundle.IdempotentRange
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Native image bundles and their literal classifying and pullback maps

The total space has its actual subspace topology in the trivial real bundle.
The native image-bundle theorem is the completed TauCeti source port, with
local model fibres supplied by actual range equivalences. No constant rank
is imposed on the whole real variety. The classifying map is the original
orthogonal projection matrix, and pullback composes that same matrix family.

Sources: Kucharz--Kurdyka, 1308.4376v1, Definitions 1.1--1.2; TauCeti
62bbc0596dc3539d488232e4e924a338548ea0a9, Topology/VectorBundle/IdempotentRange
(Apache 2.0, original source credits retained in the imported port).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealProjectionBundleMaps

open RealAlgebraicBundleStrata Bundle TopologicalSpace Topology
open scoped Matrix.Norms.Elementwise

abbrev Vectors (r : ℕ) := Fin r → ℝ
abbrev Matrices (r : ℕ) := Matrix (Fin r) (Fin r) ℝ

def matrixOperator (r : ℕ) : Matrices r →ₗ[ℝ] (Vectors r →L[ℝ] Vectors r) where
  toFun a := (Matrix.toLin' a).toContinuousLinearMap
  map_add' a b := by ext v i; simp [Matrix.toLin'_apply]
  map_smul' c a := by ext v i; simp [Matrix.toLin'_apply]

theorem matrixOperator_continuous (r : ℕ) : Continuous (matrixOperator r) :=
  (matrixOperator r).toContinuousLinearMap.continuous

variable {n r : ℕ} {X : RealVariety n} (P : ProjectionBundle X r)

def operator (x : X.locus) : Vectors r →L[ℝ] Vectors r :=
  matrixOperator r (P.projection x)

theorem operator_continuous : Continuous (operator P) :=
  (matrixOperator_continuous r).comp P.continuous

theorem operator_idempotent (x : X.locus) : IsIdempotentElem (operator P x) := by
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toLin' (P.projection x) (Matrix.toLin' (P.projection x) v) =
    Matrix.toLin' (P.projection x) v
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, P.idempotent x]

abbrev TotalSpace (F : Type*) := Bundle.TotalSpace F (fun x ↦ (operator P x).range)

theorem totalSpace_embedding (F : Type*) :
    IsEmbedding (fun v : TotalSpace P F ↦ (v.proj, (v.2 : Vectors r))) :=
  TauCeti.isEmbedding_totalSpace_range F (operator P)

theorem operator_range (x : X.locus) : (operator P x).range = P.fiber x := rfl

@[instance_reducible]
def nativeFiberBundle (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : ∀ x : X.locus, Nonempty (F ≃L[ℝ] (operator P x).range)) :
    FiberBundle F (fun x ↦ (operator P x).range) :=
  TauCeti.rangeFiberBundle (operator_continuous P) (operator_idempotent P) hF

theorem nativeVectorBundle (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : ∀ x : X.locus, Nonempty (F ≃L[ℝ] (operator P x).range)) :
    letI := nativeFiberBundle P F hF
    VectorBundle ℝ F (fun x ↦ (operator P x).range) :=
  TauCeti.rangeVectorBundle (operator_continuous P) (operator_idempotent P) hF

def trivializingOpen (x : X.locus) : Opens X.locus :=
  ⟨{y | IsUnit (operator P y * operator P x +
    (1 - operator P y) * (1 - operator P x))},
    TauCeti.isOpen_setOf_isUnit_intertwiner (operator_continuous P) x⟩

theorem mem_trivializingOpen (x : X.locus) : x ∈ trivializingOpen P x :=
  ContinuousLinearMap.IsIdempotentElem.isUnit_mul_self_add_one_sub_mul_one_sub
    (operator_idempotent P x)

def localRangeEquiv (x : X.locus) (y : trivializingOpen P x) :
    (operator P x).range ≃L[ℝ] (operator P y.val).range :=
  ContinuousLinearMap.IsIdempotentElem.rangeEquiv
    (operator_idempotent P x) (operator_idempotent P y.val) y.property

/-- Every projection family has a native bundle on this actual neighbourhood,
even when its rank varies across different components of the whole variety. -/
@[instance_reducible]
def localFiberBundle (x : X.locus) :
    FiberBundle (operator P x).range
      (fun y : trivializingOpen P x ↦ (operator P y.val).range) :=
  TauCeti.rangeFiberBundle ((operator_continuous P).comp continuous_subtype_val)
    (fun y ↦ operator_idempotent P y.val) (fun y ↦ ⟨localRangeEquiv P x y⟩)

theorem localVectorBundle (x : X.locus) :
    letI := localFiberBundle P x
    VectorBundle ℝ (operator P x).range
      (fun y : trivializingOpen P x ↦ (operator P y.val).range) :=
  TauCeti.rangeVectorBundle ((operator_continuous P).comp continuous_subtype_val)
    (fun y ↦ operator_idempotent P y.val) (fun y ↦ ⟨localRangeEquiv P x y⟩)

/-- The disjoint union of the orthogonal-projection models of real Grassmannians. -/
abbrev OrthogonalProjector (r : ℕ) :=
  {a : Matrices r // a * a = a ∧ a.transpose = a}

def classifying : X.locus → OrthogonalProjector r :=
  fun x ↦ ⟨P.projection x, P.idempotent x, P.symmetric x⟩

theorem classifying_continuous : Continuous (classifying P) :=
  P.continuous.subtype_mk _

theorem classifying_fiber (x : X.locus) :
    LinearMap.range (Matrix.toLin' (classifying P x).val) = P.fiber x := rfl

/-- Regularity is tested on the actual entries of the displayed classifying map. -/
def classifyingRegularOn (S : Set (Ambient n)) : Prop :=
  EntrywiseRegularOn (fun x ↦ (classifying P x).val) S

theorem classifyingRegularOn_iff (S : Set (Ambient n)) :
    classifyingRegularOn P S ↔ IsAlgebraicOn P S := Iff.rfl

/-- Actual locally rational maps of embedded real varieties: a continuous map of real points
whose coordinates are regular functions on the source locus. Only the values on the source locus
are data, so two regular maps with the same map of points are equal (`RegularMap.ext`). -/
@[ext]
structure RegularMap {a b : ℕ} (X : RealVariety a) (Y : RealVariety b) where
  /-- The map of real points. -/
  map : X.locus → Y.locus
  /-- Each coordinate is regular on the source locus. `RegularOn` only reads values on the locus,
  so this is tested on every ambient extension of the coordinate (one exists: zero elsewhere). -/
  regular : ∀ i : Fin b, ∀ f : Ambient a → ℝ, (∀ x : X.locus, f x.val = (map x).val i) →
    RegularOn X.locus f
  /-- The map of real points is continuous for the Euclidean topologies. -/
  map_continuous : Continuous map

def pullback {m : ℕ} (Y : RealVariety m) (f : Y.locus → X.locus)
    (hf : Continuous f) : ProjectionBundle Y r where
  projection := P.projection ∘ f
  continuous := P.continuous.comp hf
  idempotent y := P.idempotent (f y)
  symmetric y := P.symmetric (f y)

theorem pullback_fiber {m : ℕ} (Y : RealVariety m) (f : Y.locus → X.locus)
    (hf : Continuous f) (y : Y.locus) : (pullback P Y f hf).fiber y = P.fiber (f y) := rfl

theorem pullback_classifying {m : ℕ} (Y : RealVariety m) (f : Y.locus → X.locus)
    (hf : Continuous f) : classifying (pullback P Y f hf) = classifying P ∘ f := rfl

def regularPullback {m : ℕ} (Y : RealVariety m) (f : RegularMap Y X) : ProjectionBundle Y r :=
  pullback P Y f.map f.map_continuous

theorem regularPullback_fiber {m : ℕ} (Y : RealVariety m) (f : RegularMap Y X)
    (y : Y.locus) : (regularPullback P Y f).fiber y = P.fiber (f.map y) := rfl

end MathlibExt.AlgebraicGeometry.RealProjectionBundleMaps
