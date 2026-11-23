/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2.lean`
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

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- A section of an additive fppf sheaf over a faithfully flat, finitely
presented algebra descends uniquely to the base when its two pullbacks to
the tensor square agree. -/
public theorem existsUnique_section_of_map_i1_eq_map_i2
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1})
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (CommRingCat.ofHom
        Algebra.TensorProduct.includeLeftRingHom)).op e =
      E.obj.map (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).toRingHom)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e := by
  classical
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := A)⟩
  have hcov : Sieve.generate (Presieve.singleton
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ∈
      Scheme.fppfTopology (Spec (.of R)) :=
    Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _)
  have hsh : Presheaf.IsSheaf Scheme.fppfTopology (E.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ E.obj (CategoryTheory.forget _)).mp E.property
  have hsf : Presieve.IsSheafFor (E.obj ⋙ CategoryTheory.forget AddCommGrpCat)
      (Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh.isSheafFor _ hcov
  rw [Presieve.isSheafFor_singleton] at hsf
  refine hsf e ?_
  intro Z p₁ p₂ hp
  change E.obj.map p₁.op e = E.obj.map p₂.op e
  set q : Z ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    Limits.pullback.lift p₁ p₂ hp with hq
  have h1 : p₁ = q ≫ (pullbackSpecIso R A A).hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [pullbackSpecIso_hom_fst, hq, Limits.pullback.lift_fst]
  have h2 : p₂ = q ≫ (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom
      ↑(Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A))) := by
    rw [pullbackSpecIso_hom_snd, hq, Limits.pullback.lift_snd]
  rw [h1, h2]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact congrArg _ (congrArg _ he)

end AlgebraicGeometry.Scheme
