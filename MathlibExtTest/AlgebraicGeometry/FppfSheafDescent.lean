/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FppfSheafDescent

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

private theorem exactSource
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1})
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (CommRingCat.ofHom
        Algebra.TensorProduct.includeLeftRingHom)).op e =
      E.obj.map (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).toRingHom)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e :=
  AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2 E R A e he

-- The same statement at the next universe level.
example
    (E : Sheaf Scheme.fppfTopology.{u + 1} AddCommGrpCat.{u + 2})
    (R A : Type (u + 1)) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (CommRingCat.ofHom
        Algebra.TensorProduct.includeLeftRingHom)).op e =
      E.obj.map (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).toRingHom)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e :=
  AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2 E R A e he
