/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingle
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientWaldhausen
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality

/-!
# Single-degree embeddings and the Waldhausen S-construction

For a preadditive category `E` with a zero object and `j : ℤ`, the functor `single E j` places
an object in cochain degree `j` and gives it zero terms in all other degrees. It preserves
every specified pushout square. If `E` is exact and has binary biproducts, an admissible
monomorphism gives an admissible monomorphism in every term of the corresponding single-degree
map.

Let `A` be an abelian category and `F : E ⥤ A` additive. With admissible cofibrations and
isomorphism weak equivalences on `E`, and degreewise admissible cofibrations and
quasi-isomorphisms after applying `F` on bounded complexes, `single E j` preserves
cofibrations, weak equivalences, and pushouts along cofibrations. Its maps on S-construction
diagrams are postcomposition by `single E j`. Evaluation in degree `j` recovers each diagram
through the single-term isomorphisms, and these maps commute with reindexing by finite-ordinal
maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Let `E` be a preadditive exact category with a zero object and binary biproducts. For `j : ℤ`,
objects `X, Y : E`, and an admissible monomorphism `f : X ⟶ Y`, the bounded cochain map
`(single E j).map f` is degreewise an admissible monomorphism. Its degree-`j` component is
identified with `f`; all remaining components are between zero objects. -/
theorem single_map_degreewiseAdmissibleMonomorphisms (j : ℤ) {X Y : E} (f : X ⟶ Y)
    (hf : IsAdmissibleMono f) : degreewiseAdmissibleMonomorphisms E ((single E j).map f) := by
  intro i
  by_cases hi : i = j
  · subst i
    rw [single_map_f_self]
    exact admissibleMono_comp.comp_mem _ _
      (IsAdmissibleMono.of_isIso (singleObjXSelf E j X).hom)
      (admissibleMono_comp.comp_mem _ _ hf
        (IsAdmissibleMono.of_isIso (singleObjXSelf E j Y).inv))
  · let e := (single_isZero_X E j X i hi).isoZero
    have h : IsAdmissibleMono (e.inv ≫ ((single E j).map f).hom.f i) :=
      IsAdmissibleMono.fromZero _
    have hcomp : IsAdmissibleMono (e.hom ≫ (e.inv ≫ ((single E j).map f).hom.f i)) :=
      admissibleMono_comp.comp_mem e.hom
        (e.inv ≫ ((single E j).map f).hom.f i) (IsAdmissibleMono.of_isIso e.hom) h
    simpa only [Iso.hom_inv_id_assoc] using hcomp

omit [ExactCategory E] [HasBinaryBiproducts E] in
/-- Let `E` be a preadditive category with a zero object, and let `j : ℤ`. Suppose `i : X ⟶ Y`, `f
: X ⟶ Z`, `inY : Y ⟶ P`, and `inZ : Z ⟶ P` form a pushout square in `E`. Their images under
`single E j : E ⥤ Bounded E` form a pushout square with apex `(single E j).obj P`. The
hypothesis is the specified pushout square; exactness and binary biproducts are not required
for this statement. -/
theorem single_map_isPushout (j : ℤ) {X Y Z P : E}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) :
    IsPushout ((single E j).map i) ((single E j).map f)
      ((single E j).map inY) ((single E j).map inZ) := by
  have hRaw := hP.map (HomologicalComplex.single E (.up ℤ) j)
  exact IsPushout.of_map_of_faithful (ι E) hRaw

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.IsExact]

omit [F.IsExact] in
/-- Let `E : Type uE` be a preadditive exact category with morphisms in universe `vE`, a zero
object, and binary biproducts. Let `A : Type uA` be abelian with morphisms in universe `vA`,
and let `F : E ⥤ A` be additive. Equip `E` with admissible monomorphisms and isomorphism weak
equivalences, and `Bounded E` with degreewise admissible monomorphisms and maps that become
quasi-isomorphisms after applying `F`. For every `j : ℤ`, `single E j` is Waldhausen exact: it
preserves cofibrations, weak equivalences, and pushout squares along cofibrations. -/
theorem single_isWaldhausenExact (j : ℤ) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    (single E j).IsWaldhausenExact := by
  let _ : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  let _ : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  let S := single E j
  let _ : S.Additive := by
    dsimp only [S, single]
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact S.map_isZero hX
  · intro X Y f hf
    apply (ambient_isCofibration_iff F _).2
    change IsAdmissibleMono f at hf
    exact single_map_degreewiseAdmissibleMonomorphisms j f hf
  · intro X Y f hf
    change IsIso f at hf
    let _ : IsIso f := hf
    apply (ambient_isWeakEquivalence_iff F _).2
    let G := HomologicalComplex.single E (.up ℤ) j ⋙ F.mapHomologicalComplex (.up ℤ)
    change QuasiIso (G.map f)
    infer_instance
  · intro X Y Z P i f inZ inY hi hP
    exact single_map_isPushout j hP

omit [F.IsExact] in
/-- Let `E` be a preadditive exact category with a zero object and binary biproducts, and let `F : E ⥤ A` be additive
into an abelian category. Use admissible cofibrations and isomorphism weak equivalences on `E`, and degreewise
admissible cofibrations and `F`-quasi-isomorphisms on `Bounded E`. For `j : ℤ`, `n : ℕ`, and an S-construction object `X
: Stage E n` with diagram `X.obj : Ar n ⥤ E`,
`(((single_isWaldhausenExact F j).mapStage n).obj X).obj = X.obj ⋙ single E j`.
Thus every diagram entry is replaced by its complex concentrated in degree `j`. -/
theorem single_mapStage_obj (j : ℤ) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    ∀ X : Stage E n, (((single_isWaldhausenExact F j).mapStage n).obj X).obj =
      X.obj ⋙ single E j := by
  let _ : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  let _ : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  intro X
  exact (single_isWaldhausenExact F j).mapStage_obj n X

omit [F.IsExact] in
/-- Let `E` be a preadditive exact category with a zero object and binary biproducts, and let `F : E ⥤ A` be additive
into an abelian category. Use the exact-category cofibrations and isomorphism weak equivalences on `E` and the
degreewise admissible and `F`-quasi-isomorphism structure on `Bounded E`. For `j : ℤ`, `n : ℕ`, and `f : X ⟶ Y` between
objects of `Stage E n`,
`(((single_isWaldhausenExact F j).mapStage n).map f).hom = Functor.whiskerRight f.hom (single E j)`.
The induced diagram morphism is the degreewise image of each component of `f.hom`. -/
theorem single_mapStage_map (j : ℤ) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    ∀ {X Y : Stage E n} (f : X ⟶ Y),
      (((single_isWaldhausenExact F j).mapStage n).map f).hom =
        Functor.whiskerRight f.hom (single E j) := by
  let _ : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  let _ : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  intro X Y f
  exact (single_isWaldhausenExact F j).mapStage_map n f

omit [F.IsExact] in
/-- Let `E` be a preadditive exact category with a zero object and binary biproducts, and let `F : E ⥤ A` be additive
into an abelian category. With the exact-category and bounded `F`-quasi-isomorphism structures, for `j : ℤ`, `n : ℕ`,
and `X : Stage E n`, there is a natural isomorphism of `Ar n`-diagrams
`(((single_isWaldhausenExact F j).mapStage n).obj X).obj ⋙ eval E j ≅ X.obj`.
Its components are the identifications of the degree-`j` terms of single-degree complexes with their coefficient
objects. -/
def singleStageEvaluationIso (j : ℤ) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    ∀ X : Stage E n,
      (((single_isWaldhausenExact F j).mapStage n).obj X).obj ⋙ eval E j ≅ X.obj := by
  letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  intro X
  refine NatIso.ofComponents (fun a => singleObjXSelf E j (X.obj.obj a)) ?_
  intro a b g
  change ((single E j).map (X.obj.map g)).hom.f j ≫ (singleObjXSelf E j (X.obj.obj b)).hom =
    (singleObjXSelf E j (X.obj.obj a)).hom ≫ X.obj.map g
  rw [single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [F.IsExact] in
/-- Let `E` be a preadditive exact category with a zero object and binary biproducts, and let `F : E ⥤ A` be additive
into an abelian category. For `j : ℤ`, `n : ℕ`, `X : Stage E n`, and `a : Ar n`, the evaluation isomorphism for the
diagram obtained by the single-degree embedding satisfies
`(singleStageEvaluationIso F j n X).hom.app a = (singleObjXSelf E j (X.obj.obj a)).hom`.
The right side identifies the degree-`j` term with the object at `a`. -/
theorem singleStageEvaluationIso_hom_app (j : ℤ) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    ∀ (X : Stage E n) (a : Ar n), (singleStageEvaluationIso F j n X).hom.app a =
      (singleObjXSelf E j (X.obj.obj a)).hom := by
  let _ : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  let _ : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  intro X a
  rfl

omit [F.IsExact] in
/-- Let `E` be a preadditive exact category with a zero object and binary biproducts, and let `F : E ⥤ A` be additive
into an abelian category. Use the exact-category and bounded `F`-quasi-isomorphism structures. For `j : ℤ` and `g : a ⟶
b` in `SimplexCategory`,
`reindexStage (C := E) g ⋙ (single_isWaldhausenExact F j).mapStage a.len = (single_isWaldhausenExact F j).mapStage b.len
⋙ reindexStage (C := Bounded E) g`.
This is an equality of functors from `Stage E b.len` to `Stage (Bounded E) a.len`. -/
theorem single_mapStage_reindex (j : ℤ) {a b : SimplexCategory} (g : a ⟶ b) :
    letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
    letI : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
    reindexStage (C := E) g ⋙ (single_isWaldhausenExact F j).mapStage a.len =
      (single_isWaldhausenExact F j).mapStage b.len ⋙ reindexStage (C := Bounded E) g := by
  let _ : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  let _ : WaldhausenCategoryWithoutGluing (Bounded E) := ambientWaldhausenCategory F
  exact (single_isWaldhausenExact F j).mapStage_reindex g

end CochainComplex.Bounded

end
