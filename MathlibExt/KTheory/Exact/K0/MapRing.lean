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

public import Mathlib.CategoryTheory.Monoidal.Functor
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.KTheory.Exact.K0.Ring

/-!
# Functoriality of K₀ for braided monoidal exact categories

A strong monoidal exact functor between braided monoidal exact categories
induces a ring homomorphism on the K₀ rings.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ExactCategory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [IsTensorBiexact C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [IsTensorBiexact D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [MonoidalCategory E] [BraidedCategory E] [MonoidalPreadditive E] [IsTensorBiexact E]

/-- Ring homomorphism on K₀ induced by a strong monoidal exact functor -/
noncomputable def K0.mapRing (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.IsExact] :
    K0 C →+* K0 D where
  toFun := K0.map F
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [← K0.one_eq (C := C), K0.map_mk, ← K0.one_eq (C := D)]
    exact K0.mk_congr_of_iso (Functor.Monoidal.εIso F).symm
  map_mul' x y := by
    have key : (AddMonoidHom.mul.compr₂ (K0.map F) : K0 C →+ K0 C →+ K0 D)
        = (AddMonoidHom.mul.comp (K0.map F)).compl₂ (K0.map F) :=
      K0.hom_ext fun X => K0.hom_ext fun Y => by
        simp [K0.mk_congr_of_iso (Functor.Monoidal.μIso F X Y).symm]
    exact DFunLike.congr_fun (DFunLike.congr_fun key x) y

/-- Forgetting multiplication from the induced `K₀` ring homomorphism recovers the existing
additive `K₀` map. -/
@[simp]
lemma K0.mapRing_toAddMonoidHom (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.IsExact] :
    (K0.mapRing F).toAddMonoidHom = K0.map F :=
  rfl

/-- `K₀` as a ring functor respects identities. -/
lemma K0.mapRing_id :
    K0.mapRing (𝟭 C) = RingHom.id (K0 C) := by
  ext a : 1
  change K0.map (𝟭 C) a = a
  exact DFunLike.congr_fun K0.map_id a

/-- `K₀` as a ring functor respects composition. -/
lemma K0.mapRing_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.Monoidal]
    [G.Monoidal] [F.IsExact] [G.IsExact] :
    K0.mapRing (F.comp G) = (K0.mapRing G).comp (K0.mapRing F) := by
  ext a : 1
  change K0.map (F.comp G) a = K0.map G (K0.map F a)
  exact DFunLike.congr_fun (K0.map_comp F G) a

/-- If `F` and `G` are naturally isomorphic strong monoidal exact functors, they induce the same
ring homomorphism on `K₀`. -/
theorem K0.mapRing_eq_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] [F.Monoidal]
    [G.Monoidal] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    K0.mapRing F = K0.mapRing G := by
  have h : (K0.mapRing F).toAddMonoidHom = (K0.mapRing G).toAddMonoidHom := by
    rw [K0.mapRing_toAddMonoidHom, K0.mapRing_toAddMonoidHom, K0.map_eq_of_iso e]
  exact RingHom.ext fun a => DFunLike.congr_fun h a

end AlgebraicKTheory
