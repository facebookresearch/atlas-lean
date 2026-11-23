/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean`
and
`P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Tactic.Algebraize
public import MathlibExt.Algebra.TensorProduct.Domain

/-!
# Geometrically irreducible schemes over an algebraically closed field

An irreducible scheme over an algebraically closed field is geometrically
irreducible: every base change to a field extension stays irreducible. The
key algebraic input is that the tensor product of a residue field with a
field extension over an algebraically closed field is a domain.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GeometricallyIrreducibleAux

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K]

/-- The fiber of the base-changed projection over a point is the spectrum of
the tensor product of the residue field with the base-change field, hence
irreducible. -/
private theorem irreducibleSpace_fiber_fst (x : X) :
    IrreducibleSpace
      ↥((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fiber x) := by
  set i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) with hi
  let g := X.fromSpecResidueField x
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ f)
  algebraize [φ.hom]
  let e : (pullback.fst f i).fiber x ≅ Spec (CommRingCat.of (X.residueField x ⊗[k] K)) :=
    (pullbackSymmetry (pullback.fst f i) g) ≪≫ (pullbackRightPullbackFstIso f i g) ≪≫
      (pullback.congrHom hφ.symm rfl) ≪≫ pullbackSpecIso k (X.residueField x) K
  haveI : IsDomain (X.residueField x ⊗[k] K) :=
    Algebra.TensorProduct.isDomain_of_isAlgClosed_of_field (X.residueField x) K
  haveI : IrreducibleSpace ↥(Spec (CommRingCat.of (X.residueField x ⊗[k] K))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (X.residueField x ⊗[k] K)))
  exact e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

/-- The base change of an irreducible scheme over an algebraically closed
field to any field extension is irreducible. -/
private theorem irreducibleSpace_pullback [IrreducibleSpace X] :
    IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  set i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) with hi
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Surjective i := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  haveI : Surjective (pullback.fst f i) := inferInstance
  have hopen : IsOpenMap (pullback.fst f i) := (pullback.fst f i).isOpenMap
  have hsurj : Function.Surjective (pullback.fst f i) := (pullback.fst f i).surjective
  rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.preimage_univ (f := (pullback.fst f i))]
  refine (IrreducibleSpace.isIrreducible_univ X).preimage_of_isPreirreducible_fiber
    (pullback.fst f i) hopen (fun x => ?_) ?_
  · rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    haveI := irreducibleSpace_fiber_fst f K x
    exact ((IrreducibleSpace.isIrreducible_univ _).image _
      ((pullback.fst f i).fiberι x).continuous.continuousOn).isPreirreducible
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, hz⟩ := hsurj x
    exact ⟨x, Set.mem_univ x, z, hz⟩

end GeometricallyIrreducibleAux

namespace AlgebraicGeometry

/-- An irreducible scheme over an algebraically closed field is geometrically
irreducible. -/
theorem GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IrreducibleSpace X] :
    GeometricallyIrreducible f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} => IrreducibleSpace Y)).mpr fun K _ _ => ?_⟩
  exact GeometricallyIrreducibleAux.irreducibleSpace_pullback f K

end AlgebraicGeometry
