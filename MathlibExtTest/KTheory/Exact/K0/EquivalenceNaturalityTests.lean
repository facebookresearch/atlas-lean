/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.KTheory.Exact.K0.EquivalenceNaturality

/-!
# Public clients for whole K₀ ring comparison squares

All four category object and Hom universes remain independent. The clients
use the actual ring maps and literal original inverse functions. Equivalence
inverses are additive and exact; no inverse monoidal structure is supplied.
-/

open CategoryTheory Limits
open AlgebraicKTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [ExactCategory.IsTensorBiexact C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]
  [ExactCategory.IsTensorBiexact D]
variable {C' : Type u₃} [Category.{v₃} C'] [Preadditive C']
  [HasZeroObject C'] [HasBinaryBiproducts C'] [ExactCategory C']
  [MonoidalCategory C'] [BraidedCategory C'] [MonoidalPreadditive C']
  [ExactCategory.IsTensorBiexact C']
variable {D' : Type u₄} [Category.{v₄} D'] [Preadditive D']
  [HasZeroObject D'] [HasBinaryBiproducts D'] [ExactCategory D']
  [MonoidalCategory D'] [BraidedCategory D'] [MonoidalPreadditive D']
  [ExactCategory.IsTensorBiexact D']

variable (e : C ≌ D) (e' : C' ≌ D')
  [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
  [e.functor.Monoidal]
  [e'.functor.Additive] [e'.inverse.Additive] [e'.functor.IsExact] [e'.inverse.IsExact]
  [e'.functor.Monoidal]
variable (F : C ⥤ C') (G : D ⥤ D')
  [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] [F.Monoidal] [G.Monoidal]
variable (n : F ⋙ e'.functor ≅ e.functor ⋙ G)

example :
    (K0.ringEquivOfEquivalence e' : K0 C' →+* K0 D').comp (K0.mapRing F) =
      (K0.mapRing G).comp (K0.ringEquivOfEquivalence e : K0 C →+* K0 D) :=
  K0.ringEquivOfEquivalence_naturality e e' F G n

example :
    ((K0.ringEquivOfEquivalence e').symm : K0 D' →+* K0 C').comp (K0.mapRing G) =
      (K0.mapRing F).comp ((K0.ringEquivOfEquivalence e).symm : K0 D →+* K0 C) :=
  K0.ringEquivOfEquivalence_symm_naturality e e' F G n

example (x : K0 C) :
    K0.map e'.functor (K0.mapRing F x) = K0.mapRing G (K0.map e.functor x) := by
  exact DFunLike.congr_fun (K0.ringEquivOfEquivalence_naturality e e' F G n) x

example (y : K0 D) :
    K0.map e'.inverse (K0.mapRing G y) = K0.mapRing F (K0.map e.inverse y) := by
  exact DFunLike.congr_fun (K0.ringEquivOfEquivalence_symm_naturality e e' F G n) y

example :
    (K0.ringEquivOfEquivalence e : K0 C →+* K0 D).comp (RingHom.id (K0 C)) =
      (RingHom.id (K0 D)).comp (K0.ringEquivOfEquivalence e : K0 C →+* K0 D) := by
  have hn := K0.ringEquivOfEquivalence_naturality e e (𝟭 C) (𝟭 D)
    (Functor.leftUnitor e.functor ≪≫ (Functor.rightUnitor e.functor).symm)
  simpa only [K0.mapRing_id] using hn

example :
    ((K0.ringEquivOfEquivalence e).symm : K0 D →+* K0 C).comp (RingHom.id (K0 D)) =
      (RingHom.id (K0 C)).comp ((K0.ringEquivOfEquivalence e).symm : K0 D →+* K0 C) := by
  have hn := K0.ringEquivOfEquivalence_symm_naturality e e (𝟭 C) (𝟭 D)
    (Functor.leftUnitor e.functor ≪≫ (Functor.rightUnitor e.functor).symm)
  simpa only [K0.mapRing_id] using hn

#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_naturality
#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_symm_naturality
