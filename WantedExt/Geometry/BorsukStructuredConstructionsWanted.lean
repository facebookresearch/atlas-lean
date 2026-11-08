/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The strongly regular input and projected-point construction
-/
module

public import Batteries.Util.ProofWanted

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Geometry.Euclidean.BorsukNumber

@[expose] public section

namespace WantedExt.Geometry.BorsukStructuredConstructionsWanted

open Metric

/-- Points of the projective plane over the field with sixteen elements.
Source: Grinsztajn (2026), Section 2, Brouwer's projective model. -/
private abbrev BrouwerProjectivePoint :=
  Projectivization (GaloisField 2 4) (Fin 3 → GaloisField 2 4)

/-- The source Hermitian form, evaluated on chosen nonzero projective representatives.
Source: Grinsztajn (2026), Section 2, Hermitian form over the field of order sixteen. -/
private noncomputable def brouwerHermitianForm (u v : BrouwerProjectivePoint) : GaloisField 2 4 :=
  ∑ i : Fin 3, u.rep i * (v.rep i) ^ 4

/-- Unordered orthogonal triples of non-isotropic projective points.
Source: Grinsztajn (2026), Section 2, vertices of the projective model. -/
private def BrouwerOrthogonalBasis :=
  {A : Finset BrouwerProjectivePoint // A.card = 3 ∧
    (∀ u ∈ A, brouwerHermitianForm u u ≠ 0) ∧
    ∀ u ∈ A, ∀ v ∈ A, u ≠ v → brouwerHermitianForm u v = 0}

/-- Isotropic points on the three projective lines belonging to an orthogonal triple.
Source: Grinsztajn (2026), Section 2, the associated isotropic set T(A). -/
private def brouwerIsotropicTriangle (A : BrouwerOrthogonalBasis) : Set BrouwerProjectivePoint :=
  {q | brouwerHermitianForm q q = 0 ∧
    ∃ u ∈ A.val, ∃ v ∈ A.val, u ≠ v ∧
      q.rep ∈ Submodule.span (GaloisField 2 4) {u.rep, v.rep}}

/-- Two distinct triples are adjacent when their isotropic triangles meet in three points.
Source: Grinsztajn (2026), Section 2, adjacency of the projective model. -/
private noncomputable def brouwerG2FourGraph : SimpleGraph BrouwerOrthogonalBasis := by
  classical
  exact {
    Adj := fun A B => A ≠ B ∧
      (brouwerIsotropicTriangle A ∩ brouwerIsotropicTriangle B).ncard = 3
    symm := ⟨by
      intro A B h
      simpa [Set.inter_comm, ne_comm] using h⟩
    loopless := ⟨by
      intro A h
      exact h.1 rfl⟩ }

/-- Finiteness of the source projective plane.
Source: Grinsztajn (2026), Section 2; Mathlib's finite-quotient API. -/
private instance brouwerProjectivePointFinite : Finite BrouwerProjectivePoint := by
  change Finite (Quotient _)
  infer_instance

/-- Finiteness of the source's orthogonal triples.
Source: Grinsztajn (2026), Section 2; finite subsets of the finite projective plane. -/
private instance brouwerOrthogonalBasisFinite : Finite BrouwerOrthogonalBasis := by
  classical
  let : Fintype BrouwerProjectivePoint := Fintype.ofFinite BrouwerProjectivePoint
  change Finite {A : Finset BrouwerProjectivePoint // _}
  infer_instance

/-- The graph's adjacency is exactly the source three-point triangle intersection.
Source: Grinsztajn (2026), Section 2, adjacency of the projective model. -/
private theorem brouwerG2FourGraph_adj_iff (A B : BrouwerOrthogonalBasis) :
    brouwerG2FourGraph.Adj A B ↔ A ≠ B ∧
      (brouwerIsotropicTriangle A ∩ brouwerIsotropicTriangle B).ncard = 3 :=
  Iff.rfl

/-- Every graph vertex consists of precisely three projective points.
Source: Grinsztajn (2026), Section 2, unordered orthogonal triples. -/
private theorem brouwerOrthogonalBasis_card (A : BrouwerOrthogonalBasis) : A.val.card = 3 :=
  A.prop.1


/-- The concrete Brouwer graph and its Euclidean two-distance input. This is an unproved claim.
Source: Grinsztajn (2026), Sections 2 and 3. -/
private theorem_wanted stronglyRegularCounterexampleInputs : (by
  classical
  exact ∃ e : BrouwerOrthogonalBasis ≃ Fin 416,
    let G := brouwerG2FourGraph.comap e.symm
    G.IsSRGWith 416 100 36 20 ∧
    (∀ A : BrouwerOrthogonalBasis, (brouwerIsotropicTriangle A).ncard = 15) ∧
    ∃ x : Fin 416 → EuclideanSpace ℝ (Fin 65),
      Function.Injective x ∧
      (∀ u v, inner ℝ (x u) (x v) =
        if u = v then 90 else if G.Adj u v then 18 else -6) ∧
      IsTwoDistanceSet (Set.range x))

/-- The 352-point codimension-one restriction of the concrete graph input. This is unproved.
Source: Optimization Problems, constant 28a, [JB2014-ub-64]. -/
private theorem_wanted jenrichBrouwerStructuredConstruction : (by
  classical
  exact ∃ (e : BrouwerOrthogonalBasis ≃ Fin 416)
      (x : Fin 416 → EuclideanSpace ℝ (Fin 65)) (B : Fin 3 → Finset (Fin 416)),
    let G := brouwerG2FourGraph.comap e.symm
    let C := Finset.univ \ (Finset.univ.biUnion B)
    let S : Fin 3 → EuclideanSpace ℝ (Fin 65) := fun i => ∑ v ∈ B i, x v
    let W := (Submodule.span ℝ {S 1 - S 2})ᗮ
    let A := C ∪ B 0
    G.IsSRGWith 416 100 36 20 ∧ Function.Injective x ∧
    (∀ u v, inner ℝ (x u) (x v) =
      if u = v then 90 else if G.Adj u v then 18 else -6) ∧
    (∀ i, (B i).card = 32) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    C.card = 320 ∧ A.card = 352 ∧ Module.finrank ℝ W = 64 ∧
    (∀ a ∈ A, x a ∈ W) ∧
    ∃ φ : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 64),
      let X := φ '' {y : W | (y : EuclideanSpace ℝ (Fin 65)) ∈ x '' (A : Set (Fin 416))}
      X.ncard = 352 ∧ IsTwoDistanceSet X ∧
      (∀ Y ⊆ X, ediam Y < ediam X → Y.ncard ≤ 5) ∧
      ¬HasBorsukCover 70 X ∧ (71 : ℕ∞) ≤ setBorsukNumber X)

/-- The codimension-two subconfiguration and one scaled projected point.
This is an unproved claim.
Source: Grinsztajn (2026), Sections 4-6. -/
private theorem_wanted grinsztajnProjectedPointConstruction : (by
  classical
  exact ∃ (e : BrouwerOrthogonalBasis ≃ Fin 416)
      (x : Fin 416 → EuclideanSpace ℝ (Fin 65)) (B : Fin 3 → Finset (Fin 416))
      (b : Fin 416),
    let G := brouwerG2FourGraph.comap e.symm
    let C := Finset.univ \ (Finset.univ.biUnion B)
    let S : Fin 3 → EuclideanSpace ℝ (Fin 65) := fun i => ∑ v ∈ B i, x v
    let U := Submodule.span ℝ (Set.range S)
    let W := Uᗮ
    let z : EuclideanSpace ℝ (Fin 65) := W.orthogonalProjectionOnto (x b)
    let t : ℝ := (Real.sqrt 222 - 1) / 13
    let p := t • z
    let X := (x '' (C : Set (Fin 416))) ∪ {p}
    G.IsSRGWith 416 100 36 20 ∧ Function.Injective x ∧
    (∀ u v, inner ℝ (x u) (x v) =
      if u = v then 90 else if G.Adj u v then 18 else -6) ∧
    (∀ i, (B i).card = 32) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    C.card = 320 ∧ b ∈ B 0 ∧
    Module.finrank ℝ U = 2 ∧ Module.finrank ℝ W = 63 ∧
    (∀ c ∈ C, x c ∈ W) ∧
    z = x b - (1 / 32 : ℝ) • S 0 ∧ ‖z‖ ^ 2 = 78 ∧
    0 < t ∧ 78 * t ^ 2 + 12 * t = 102 ∧
    (∀ c ∈ C, dist p (x c) ^ 2 = if G.Adj b c then 192 - 48 * t else 192) ∧
    X.ncard = 321 ∧ ediam X = ENNReal.ofReal (Real.sqrt 192) ∧
    (∀ Y ⊆ X, ediam Y < ediam X → Y.ncard ≤ 5) ∧
    ∃ φ : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 63),
      let X₆₃ := φ '' {y : W | (y : EuclideanSpace ℝ (Fin 65)) ∈ X}
      X₆₃.ncard = 321 ∧ ¬HasBorsukCover 64 X₆₃ ∧
        (65 : ℕ∞) ≤ setBorsukNumber X₆₃)

end WantedExt.Geometry.BorsukStructuredConstructionsWanted
