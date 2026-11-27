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

public import MathlibExt.CategoryTheory.Products.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Exactness of product projections, paired functors, and the diagonal

For exact categories `C` and `D` with the componentwise product exact structure,
the projections `Prod.fst C D` and `Prod.snd C D` are exact functors: an
admissible short complex in `C × D` projects to admissible short complexes in
each factor. For exact functors `F : A ⥤ C` and `G : A ⥤ D`, the pairing
`F.prod' G` is exact into `C × D`: admissibility is componentwise via
`prodIsAdmissibleExact`, using `Functor.prod'CompFst/Snd` with
`ShortComplex.mapNatIso`, `ShortComplex.map_comp`, and `isAdmissibleExact_of_iso`.
For an exact category `C`, the diagonal `Functor.diag C : C ⥤ C × C` is exact
as the direct corollary pairing the two identity exact functors.

Nonclaims: no two-source product (`Functor.prod`) or
biproduct-functor exactness; no Waldhausen additivity; no K-theory or G-theory;
no realization; no spectra; no Q/S comparison.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (A : Type u₃) [Category.{v₃} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [ExactCategory A]

/-- The first product projection is exact for the componentwise exact structure. -/
instance prodFstIsExact : (Prod.fst C D).IsExact where
  map_admissibleExact _ hS := ((prod_isAdmissibleExact_iff C D _).mp hS).1

/-- The second product projection is exact for the componentwise exact structure. -/
instance prodSndIsExact : (Prod.snd C D).IsExact where
  map_admissibleExact _ hS := ((prod_isAdmissibleExact_iff C D _).mp hS).2

/-- Pairing of exact functors into a product is exact for the componentwise structure. -/
instance prodPairingIsExact (F : A ⥤ C) (G : A ⥤ D) [F.Additive] [G.Additive]
    [F.IsExact] [G.IsExact] : (F.prod' G).IsExact where
  map_admissibleExact S hS := by
    have hF : ExactCategory.IsAdmissibleExact (S.map F) :=
      Functor.map_admissibleExact F S hS
    have hG : ExactCategory.IsAdmissibleExact (S.map G) :=
      Functor.map_admissibleExact G S hS
    have eF : S.map F ≅ S.map ((F.prod' G) ⋙ Prod.fst C D) :=
      (S.mapNatIso (Functor.prod'CompFst F G)).symm
    have eG : S.map G ≅ S.map ((F.prod' G) ⋙ Prod.snd C D) :=
      (S.mapNatIso (Functor.prod'CompSnd F G)).symm
    have hCompF : ExactCategory.IsAdmissibleExact
        (S.map ((F.prod' G) ⋙ Prod.fst C D)) :=
      ExactCategory.isAdmissibleExact_of_iso eF hF
    have hCompG : ExactCategory.IsAdmissibleExact
        (S.map ((F.prod' G) ⋙ Prod.snd C D)) :=
      ExactCategory.isAdmissibleExact_of_iso eG hG
    have hFst : ExactCategory.IsAdmissibleExact
        ((S.map (F.prod' G)).map (Prod.fst C D)) := by
      simpa [ShortComplex.map_comp] using hCompF
    have hSnd : ExactCategory.IsAdmissibleExact
        ((S.map (F.prod' G)).map (Prod.snd C D)) := by
      simpa [ShortComplex.map_comp] using hCompG
    exact (prod_isAdmissibleExact_iff C D _).mpr ⟨hFst, hSnd⟩

/-- The diagonal functor is additive, as the pairing of two identities. -/
instance diagAdditive : (Functor.diag C).Additive := by
  unfold Functor.diag
  infer_instance

/-- The diagonal functor is exact, as the pairing of two identities. -/
instance diagIsExact : (Functor.diag C).IsExact := by
  unfold Functor.diag
  infer_instance

end CategoryTheory
