/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionNormalizationSign

/- Proof implementation note.
## # Canonical natural scalar correction of the retained acyclic comparison
-/

/-!
# Natural scalar normalization of acyclic comparisons

The scalar `σ_n=(-1)^(n(n+1)/2)` defines a natural automorphism
of any functor into a preadditive category. For a right-exact
additive functor on an abelian category with projective resolutions,
it corrects the acyclic comparison to the canonical projective comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/- Proof implementation note.
The triangular scalar correction is natural on any original degree functor.
-/

/-- For any functor `G : C → D`, where `C` is a category and
`D` preadditive, `σ_n=(-1)^(n(n+1)/2)` defines a natural
automorphism of `G` by scalar multiplication on each `G(X)`. -/
def acyclicResolutionNormalizationIso (G : C ⥤ D) (n : ℕ) : G ≅ G :=
  NatIso.ofComponents (fun X =>
    ProjectiveResolution.acyclicResolutionNormalizationIso (G.obj X) n) (fun f => by
      dsimp only [ProjectiveResolution.acyclicResolutionNormalizationIso]
      rw [comp_zsmul, zsmul_comp, Category.comp_id, Category.id_comp])

/- Proof implementation note.
Every component is the exact original triangular scalar on the original functor object.
-/

/-- For a functor `G : C → D` with `D` preadditive, the
component at `X` of its degree-`n` normalization automorphism
is `σ_n • 𝟙 G(X)`, where `σ_n=(-1)^(n(n+1)/2)`. -/
theorem acyclicResolutionNormalizationIso_hom_app (G : C ⥤ D) (n : ℕ) (X : C) :
    (G.acyclicResolutionNormalizationIso n).hom.app X =
      ProjectiveResolution.acyclicResolutionNormalizationSign n • 𝟙 (G.obj X) := rfl

/- Proof implementation note.
The correction commutes with every original coefficient natural transformation.
-/

/-- For functors `G,H : C → D` into a preadditive category and
any natural transformation `α : G → H`, the normalization
automorphisms commute with `α`: `σ_n(G) ≫ α = α ≫ σ_n(H)`. -/
theorem acyclicResolutionNormalizationIso_naturality_transformation
    {G H : C ⥤ D} (α : G ⟶ H) (n : ℕ) :
    (G.acyclicResolutionNormalizationIso n).hom ≫ α =
      α ≫ (H.acyclicResolutionNormalizationIso n).hom := by
  ext X
  simp only [NatTrans.comp_app, acyclicResolutionNormalizationIso_hom_app,
    zsmul_comp, comp_zsmul, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
The inverse of the SAME retained projective acyclic comparison has the SAME proved triangular
sign.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`P` resolving `X` with every term `F`-acyclic. In degree `n`,
the inverse acyclic comparison is `σ_n` times the inverse
canonical projective comparison. -/
theorem normalizationAcyclicProjective_inv {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).inv =
      acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv := by
  let E := F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n
  change E.inv = acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv
  apply (cancel_mono E.hom).1
  rw [E.inv_hom_id]
  change 𝟙 _ = (acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv) ≫
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom
  rw [normalizationAcyclicProjective_hom, zsmul_comp, comp_zsmul, smul_smul,
    Iso.inv_hom_id, acyclicResolutionNormalizationSign_mul_self, one_zsmul]

/- Proof implementation note.
Correct the retained projective acyclic iso by its canonical natural source scalar.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`P` an `F`-acyclic projective resolution of `X`. Composing the
acyclic comparison with the source normalization `σ_n` gives
a comparison `L_nF(X) ≅ H_n(F(P))`. -/
def normalizedAcyclicProjectiveComparison {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerived n).obj X ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n :=
  ((F.leftDerived n).acyclicResolutionNormalizationIso n).app X ≪≫
    F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
The canonical corrected comparison is literally the SAME projective comparison in every degree.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`P` an `F`-acyclic projective resolution of `X`. The corrected
comparison has forward map equal to `P.isoLeftDerivedObj F n`
in every degree `n`. -/
theorem normalizedAcyclicProjectiveComparison_hom {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (normalizedAcyclicProjectiveComparison P F hP n).hom = (P.isoLeftDerivedObj F n).hom := by
  dsimp only [normalizedAcyclicProjectiveComparison, Iso.trans_hom]
  change (acyclicResolutionNormalizationSign n • 𝟙 ((F.leftDerived n).obj X)) ≫
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom =
      (P.isoLeftDerivedObj F n).hom
  rw [normalizationAcyclicProjective_hom, zsmul_comp, comp_zsmul, Category.id_comp,
    smul_smul, acyclicResolutionNormalizationSign_mul_self, one_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C`, `D` be abelian with projective resolutions in `C`,
`F : C → D` additive, and `S : X₁ → X₂ → X₃` short exact.
The left-derived boundary `L_(n+1)F(X₃) → L_nF(X₁)`
commutes with source and target normalization up to the
adjacent scalar `(-1)^(n+1)`. -/
theorem normalizationNativeLeftBoundary_scalar (F : C ⥤ D) [F.Additive]
    (S : ShortComplex.ShortExactSequences C) (n : ℕ) :
    (acyclicResolutionNormalizationIso ((F.leftDerived (n + 1)).obj S.obj.X₃) (n + 1)).hom ≫
      LeftDerivedDelta.LDdelta F n S.obj S.property =
    normalizationCrossSign n •
      (LeftDerivedDelta.LDdelta F n S.obj S.property ≫
        (acyclicResolutionNormalizationIso ((F.leftDerived n).obj S.obj.X₁) n).hom) := by
  dsimp only [acyclicResolutionNormalizationIso]
  rw [zsmul_comp, comp_zsmul, Category.id_comp, Category.comp_id, smul_smul]
  rfl

end CategoryTheory.ProjectiveResolution
