/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Product ring embeddings for module categories

Embedding functors `ModuleCat R ⥤ ModuleCat (R × S)` and
`ModuleCat S ⥤ ModuleCat (R × S)` via restriction of scalars along
`RingHom.fst` and `RingHom.snd`. An `R`-module is viewed as an
`(R × S)`-module via the first (resp. second) projection.
Includes additive instances and simp lemmas for objects, maps,
scalar action, and pointwise evaluation.
-/

@[expose] public section

open CategoryTheory

universe v

namespace ModuleCat

/-- Embedding `ModuleCat R ⥤ ModuleCat (R × S)` via `RingHom.fst R S`.

An `R`-module `M` is regarded as an `(R × S)`-module by `(r,s) • m = r • m`. -/
noncomputable abbrev prodEmbeddingFst (R S : Type*) [Ring R] [Ring S] :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (R × S) :=
  restrictScalars (RingHom.fst R S)

/-- Embedding `ModuleCat S ⥤ ModuleCat (R × S)` via `RingHom.snd R S`.

An `S`-module `M` is regarded as an `(R × S)`-module by `(r,s) • m = s • m`. -/
noncomputable abbrev prodEmbeddingSnd (R S : Type*) [Ring R] [Ring S] :
    ModuleCat.{v} S ⥤ ModuleCat.{v} (R × S) :=
  restrictScalars (RingHom.snd R S)

/-- Additivity of `prodEmbeddingFst`. -/
instance prodEmbeddingFst_additive (R S : Type*) [Ring R] [Ring S] :
    (prodEmbeddingFst.{v} R S).Additive :=
  inferInstance

/-- Additivity of `prodEmbeddingSnd`. -/
instance prodEmbeddingSnd_additive (R S : Type*) [Ring R] [Ring S] :
    (prodEmbeddingSnd.{v} R S).Additive :=
  inferInstance

/-- Object formula for `prodEmbeddingFst`. -/
@[simp]
theorem prodEmbeddingFst_obj (R S : Type*) [Ring R] [Ring S] (M : ModuleCat.{v} R) :
    (prodEmbeddingFst R S).obj M = (restrictScalars (RingHom.fst R S)).obj M :=
  rfl

/-- Object formula for `prodEmbeddingSnd`. -/
@[simp]
theorem prodEmbeddingSnd_obj (R S : Type*) [Ring R] [Ring S] (M : ModuleCat.{v} S) :
    (prodEmbeddingSnd R S).obj M = (restrictScalars (RingHom.snd R S)).obj M :=
  rfl

/-- Morphism formula for `prodEmbeddingFst`. -/
@[simp]
theorem prodEmbeddingFst_map {R S : Type*} [Ring R] [Ring S] {M N : ModuleCat.{v} R}
    (f : M ⟶ N) :
    (prodEmbeddingFst R S).map f = (restrictScalars (RingHom.fst R S)).map f :=
  rfl

/-- Morphism formula for `prodEmbeddingSnd`. -/
@[simp]
theorem prodEmbeddingSnd_map {R S : Type*} [Ring R] [Ring S] {M N : ModuleCat.{v} S}
    (f : M ⟶ N) :
    (prodEmbeddingSnd R S).map f = (restrictScalars (RingHom.snd R S)).map f :=
  rfl

/-- Scalar action for `prodEmbeddingFst` uses the first projection. -/
theorem prodEmbeddingFst_smul_def {R S : Type*} [Ring R] [Ring S]
    {M : ModuleCat.{v} R} (p : R × S) (m : (prodEmbeddingFst R S).obj M) :
    p • m = p.1 • (show M from m) :=
  rfl

/-- Scalar action for `prodEmbeddingSnd` uses the second projection. -/
theorem prodEmbeddingSnd_smul_def {R S : Type*} [Ring R] [Ring S]
    {M : ModuleCat.{v} S} (p : R × S) (m : (prodEmbeddingSnd R S).obj M) :
    p • m = p.2 • (show M from m) :=
  rfl

/-- Pointwise morphism formula for `prodEmbeddingFst`. -/
@[simp]
theorem prodEmbeddingFst_map_apply {R S : Type*} [Ring R] [Ring S]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    (prodEmbeddingFst R S).map f x = f x :=
  rfl

/-- Pointwise morphism formula for `prodEmbeddingSnd`. -/
@[simp]
theorem prodEmbeddingSnd_map_apply {R S : Type*} [Ring R] [Ring S]
    {M N : ModuleCat.{v} S} (f : M ⟶ N) (x : M) :
    (prodEmbeddingSnd R S).map f x = f x :=
  rfl

end ModuleCat
