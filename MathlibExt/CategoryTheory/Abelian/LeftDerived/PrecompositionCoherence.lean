/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.SquareCoherence
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

/-!
# Coherence of left-derived source-precomposition comparisons

Successive additive homology-preserving source changes give directional
left-derived comparisons compatible with functor associators. If the
source changes also preserve projectives, their precomposition
isomorphisms compose to the canonical isomorphism for the composite
functor. They respect coefficient transformations, degree-zero
augmentations and connecting maps, and satisfy identity and associativity
laws. All category object and morphism universes are independent;
only the categories in which resolutions are taken need projective
resolutions.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uE vE uA vA uB vB

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {A : Type uA} [Category.{vA} A] [Abelian A]

-- Use the public capabilities locally. Their low priority leaves the
-- existing identity/composition preservation instances first in instance search.
attribute [local instance 100] preservesFiniteLimits_of_preservesHomology
  preservesFiniteColimits_of_preservesHomology

section Unit

variable [HasProjectiveResolutions C]

/-- Let `C,A` be abelian, with projective resolutions in `C`, and
`L : C → A` additive. The inverse left-derived postcomposition
comparison for the identity target functor is `𝟙 (L_nL)` in every
degree `n`. -/
theorem leftDerivedCompIsoOfPreservesHomology_id_inv (L : C ⥤ A) [L.Additive]
    (n : ℕ) :
    (L.leftDerivedCompIsoOfPreservesHomology (𝟭 A) n).inv = 𝟙 (L.leftDerived n) := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hH := HomologicalComplex.mapHomologyFunctorIso_id_hom K n
  dsimp only [leftDerivedCompIsoOfPreservesHomology, NatIso.ofComponents]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv]
  rw [Category.assoc]
  change (P.isoLeftDerivedObj (L ⋙ 𝟭 A) n).hom ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
        (𝟭 A)).hom.app K ≫ (𝟭 A).map (P.isoLeftDerivedObj L n).inv = 𝟙 _
  rw [hH]
  change (P.isoLeftDerivedObj L n).hom ≫ 𝟙 _ ≫
    (P.isoLeftDerivedObj L n).inv = 𝟙 _
  rw [Category.id_comp, Iso.hom_inv_id]

end Unit

section Directional

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]

private theorem identityOutputSquare (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
    (L : D ⥤ A) [L.Additive] (n : ℕ) :
    leftDerivedSquareHom U (𝟭 A) L (U ⋙ L) (Functor.rightUnitor (U ⋙ L)).inv n =
      leftDerivedPrecompHomOfPreservesHomology U L n := by
  have hα : (Functor.rightUnitor (U ⋙ L)).inv = 𝟙 (U ⋙ L) := by
    apply NatTrans.ext
    funext X
    rfl
  unfold leftDerivedSquareHom
  rw [hα, NatTrans.leftDerived_id, leftDerivedCompIsoOfPreservesHomology_id_inv]
  exact (congrArg (fun t => leftDerivedPrecompHomOfPreservesHomology U L n ≫ t)
    (Category.comp_id (𝟙 ((U ⋙ L).leftDerived n)))).trans (Category.comp_id _)

variable [HasProjectiveResolutions E]

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving homology, and
`L : E → A` additive. The directional comparison for `V` at `U(X)`
followed by that for `U` at `X` equals the comparison for `U ⋙ V`
followed by the derived source associator. -/
theorem leftDerivedPrecompHomOfPreservesHomology_comp
    (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
    (V : D ⥤ E) [V.Additive] [V.PreservesHomology]
    (L : E ⥤ A) [L.Additive] (n : ℕ) (X : C) :
    (leftDerivedPrecompHomOfPreservesHomology V L n).app (U.obj X) ≫
        (leftDerivedPrecompHomOfPreservesHomology U (V ⋙ L) n).app X =
      (leftDerivedPrecompHomOfPreservesHomology (U ⋙ V) L n).app X ≫
        (NatTrans.leftDerived (Functor.associator U V L).hom n).app X := by
  let α := (Functor.rightUnitor (V ⋙ L)).inv
  let β := (Functor.rightUnitor (U ⋙ (V ⋙ L))).inv
  let α₀ := composeLeftDerivedSquare V U (U ⋙ V) (Iso.refl (U ⋙ V))
    (𝟭 A) (𝟭 A) (𝟭 A) (Functor.leftUnitor (𝟭 A))
    L (V ⋙ L) (U ⋙ (V ⋙ L)) α β
  have hα₀ : α₀ = (Functor.associator U V L).hom := by
    apply NatTrans.ext
    funext Y
    rw [composeLeftDerivedSquare_app]
    change L.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp only [Functor.map_id, Category.id_comp]
  have h := leftDerivedSquareHom_comp_with_input V U (U ⋙ V)
    (Iso.refl (U ⋙ V)) (𝟭 A) (𝟭 A) (𝟭 A) (Functor.leftUnitor (𝟭 A))
    L (V ⋙ L) (U ⋙ (V ⋙ L)) α β
    (𝟙 (V.obj (U.obj X))) (𝟙 (U.obj X)) n
  change ((L.leftDerived n).map (𝟙 _) ≫
      (leftDerivedSquareHom V (𝟭 A) L (V ⋙ L) α n).app (U.obj X)) ≫
        (((V ⋙ L).leftDerived n).map (𝟙 _) ≫
          (leftDerivedSquareHom U (𝟭 A) (V ⋙ L) (U ⋙ (V ⋙ L)) β n).app X) ≫ 𝟙 _ =
    (L.leftDerived n).map (𝟙 _ ≫ V.map (𝟙 _) ≫ 𝟙 _) ≫
      (leftDerivedSquareHom (U ⋙ V) (𝟭 A) L (U ⋙ (V ⋙ L)) α₀ n).app X at h
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at h
  rw [identityOutputSquare, identityOutputSquare, hα₀] at h
  unfold leftDerivedSquareHom at h
  rw [leftDerivedCompIsoOfPreservesHomology_id_inv] at h
  simp only [NatTrans.comp_app, NatTrans.id_app] at h
  have hLeft := congrArg (fun t =>
    (leftDerivedPrecompHomOfPreservesHomology V L n).app (U.obj X) ≫ t)
      (Category.id_comp ((leftDerivedPrecompHomOfPreservesHomology U (V ⋙ L) n).app X))
  have hRight := congrArg (fun t =>
    (leftDerivedPrecompHomOfPreservesHomology (U ⋙ V) L n).app X ≫ t)
      (Category.comp_id ((NatTrans.leftDerived (Functor.associator U V L).hom n).app X))
  exact hLeft.symm.trans (h.trans hRight)

end Directional

section Canonical

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]
  [HasProjectiveResolutions E]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology] [U.PreservesProjectiveObjects]
  (V : D ⥤ E) [V.Additive] [V.PreservesHomology] [V.PreservesProjectiveObjects]
  (L : E ⥤ A) [L.Additive]

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. The precomposition comparisons for `U,V`, with source and
target associators, give
`L_n((U ⋙ V) ⋙ L) ≅ (U ⋙ V) ⋙ L_nL`. -/
def leftDerivedPrecompIsoComp (n : ℕ) :
    ((U ⋙ V) ⋙ L).leftDerived n ≅ (U ⋙ V) ⋙ L.leftDerived n :=
  NatIso.leftDerived (Functor.associator U V L) n ≪≫
    leftDerivedPrecompIso U (V ⋙ L) n ≪≫
      isoWhiskerLeft U (leftDerivedPrecompIso V L n) ≪≫
        (Functor.associator U V (L.leftDerived n)).symm

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. At `X`, the forward composite is the derived associator,
followed by precomposition for `U` with `V ⋙ L`, then precomposition
for `V` at `U(X)`. -/
theorem leftDerivedPrecompIsoComp_hom_app (n : ℕ) (X : C) :
    (leftDerivedPrecompIsoComp U V L n).hom.app X =
      (NatTrans.leftDerived (Functor.associator U V L).hom n).app X ≫
        (leftDerivedPrecompIso U (V ⋙ L) n).hom.app X ≫
          (leftDerivedPrecompIso V L n).hom.app (U.obj X) := by
  simp only [leftDerivedPrecompIsoComp, Iso.trans_hom, NatIso.leftDerived_hom,
    Iso.symm_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id]

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. At `X`, the inverse composite is inverse precomposition for
`V` at `U(X)`, then inverse precomposition for `U`, then the inverse
derived source associator. -/
theorem leftDerivedPrecompIsoComp_inv_app (n : ℕ) (X : C) :
    (leftDerivedPrecompIsoComp U V L n).inv.app X =
      (leftDerivedPrecompIso V L n).inv.app (U.obj X) ≫
        (leftDerivedPrecompIso U (V ⋙ L) n).inv.app X ≫
          (NatTrans.leftDerived (Functor.associator U V L).inv n).app X := by
  simp only [leftDerivedPrecompIsoComp, Iso.trans_inv, NatIso.leftDerived_inv,
    Iso.symm_inv, isoWhiskerLeft_inv, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. At `X`, the two successive inverse comparisons equal the
inverse comparison for `U ⋙ V` followed by the forward derived
source associator. -/
theorem leftDerivedPrecompIso_inv_comp (n : ℕ) (X : C) :
    (leftDerivedPrecompIso V L n).inv.app (U.obj X) ≫
        (leftDerivedPrecompIso U (V ⋙ L) n).inv.app X =
      (leftDerivedPrecompIso (U ⋙ V) L n).inv.app X ≫
        (NatTrans.leftDerived (Functor.associator U V L).hom n).app X := by
  simpa only [leftDerivedPrecompHomOfPreservesHomology_eq_inv] using
    leftDerivedPrecompHomOfPreservesHomology_comp U V L n X

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. The composite precomposition isomorphism equals the canonical
precomposition isomorphism for `U ⋙ V` in every degree `n`. -/
theorem leftDerivedPrecompIsoComp_eq (n : ℕ) :
    leftDerivedPrecompIsoComp U V L n = leftDerivedPrecompIso (U ⋙ V) L n := by
  have hInv : (leftDerivedPrecompIsoComp U V L n).inv =
      (leftDerivedPrecompIso (U ⋙ V) L n).inv := by
    apply NatTrans.ext
    funext X
    let e := NatIso.leftDerived (Functor.associator U V L) n
    rw [leftDerivedPrecompIsoComp_inv_app]
    have h := leftDerivedPrecompIso_inv_comp U V L n X
    change (leftDerivedPrecompIso V L n).inv.app (U.obj X) ≫
        (leftDerivedPrecompIso U (V ⋙ L) n).inv.app X =
      (leftDerivedPrecompIso (U ⋙ V) L n).inv.app X ≫ e.hom.app X at h
    calc
      (leftDerivedPrecompIso V L n).inv.app (U.obj X) ≫
          (leftDerivedPrecompIso U (V ⋙ L) n).inv.app X ≫ e.inv.app X =
        ((leftDerivedPrecompIso V L n).inv.app (U.obj X) ≫
          (leftDerivedPrecompIso U (V ⋙ L) n).inv.app X) ≫ e.inv.app X :=
            (Category.assoc _ _ _).symm
      _ = ((leftDerivedPrecompIso (U ⋙ V) L n).inv.app X ≫ e.hom.app X) ≫
          e.inv.app X := congrArg (fun f => f ≫ e.inv.app X) h
      _ = (leftDerivedPrecompIso (U ⋙ V) L n).inv.app X := by
        rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply Iso.ext
  have h := (leftDerivedPrecompIsoComp U V L n).hom_inv_id
  rw [hInv] at h
  apply (cancel_mono (leftDerivedPrecompIso (U ⋙ V) L n).inv).1
  exact h.trans (leftDerivedPrecompIso (U ⋙ V) L n).hom_inv_id.symm

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. For `f : X → Y`, the forward composite comparison commutes
with `L_n((U ⋙ V) ⋙ L)(f)` and `L_nL(V(U(f)))`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_hom_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (((U ⋙ V) ⋙ L).leftDerived n).map f ≫
        (leftDerivedPrecompIsoComp U V L n).hom.app Y =
      (leftDerivedPrecompIsoComp U V L n).hom.app X ≫
        (L.leftDerived n).map (V.map (U.map f)) :=
  (leftDerivedPrecompIsoComp U V L n).hom.naturality f

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. For additive `M : E → A` and `α : L → M`, the forward
composite comparisons commute with `L_n((U ⋙ V) ⋙ α)` and
`(U ⋙ V) ⋙ L_nα`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_hom_naturality_functor
    {M : E ⥤ A} [M.Additive] (α : L ⟶ M) (n : ℕ) :
    NatTrans.leftDerived (whiskerLeft (U ⋙ V) α) n ≫
        (leftDerivedPrecompIsoComp U V M n).hom =
      (leftDerivedPrecompIsoComp U V L n).hom ≫
        whiskerLeft (U ⋙ V) (NatTrans.leftDerived α n) := by
  rw [leftDerivedPrecompIsoComp_eq, leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_hom_naturality_functor (U ⋙ V) α n

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. For additive `M : E → A` and `α : L → M`, the inverse
composite comparisons commute with `(U ⋙ V) ⋙ L_nα` and
`L_n((U ⋙ V) ⋙ α)`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_inv_naturality_functor
    {M : E ⥤ A} [M.Additive] (α : L ⟶ M) (n : ℕ) :
    whiskerLeft (U ⋙ V) (NatTrans.leftDerived α n) ≫
        (leftDerivedPrecompIsoComp U V M n).inv =
      (leftDerivedPrecompIsoComp U V L n).inv ≫
        NatTrans.leftDerived (whiskerLeft (U ⋙ V) α) n := by
  rw [leftDerivedPrecompIsoComp_eq, leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_inv_naturality_functor (U ⋙ V) α n

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. The forward degree-zero composite followed by the
augmentation `(U ⋙ V) ⋙ L₀L → (U ⋙ V) ⋙ L` is the canonical
augmentation of `L₀((U ⋙ V) ⋙ L)`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_hom_fromLeftDerivedZero :
    (leftDerivedPrecompIsoComp U V L 0).hom ≫
        whiskerLeft (U ⋙ V) L.fromLeftDerivedZero =
      ((U ⋙ V) ⋙ L).fromLeftDerivedZero := by
  rw [leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_hom_fromLeftDerivedZero (U ⋙ V) L

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. The inverse degree-zero composite followed by the
augmentation of `L₀((U ⋙ V) ⋙ L)` equals the augmentation
`(U ⋙ V) ⋙ L₀L → (U ⋙ V) ⋙ L`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_inv_fromLeftDerivedZero :
    (leftDerivedPrecompIsoComp U V L 0).inv ≫
        ((U ⋙ V) ⋙ L).fromLeftDerivedZero =
      whiskerLeft (U ⋙ V) L.fromLeftDerivedZero := by
  rw [leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_inv_fromLeftDerivedZero (U ⋙ V) L

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. For short exact `S`, the forward composite comparisons in
degrees `n+1,n` commute with the connecting maps of `((U ⋙ V) ⋙ L)`
on `S` and of `L` on `(U ⋙ V)(S)`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_hom_LDdelta
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (leftDerivedPrecompIsoComp U V L (n + 1)).hom.app S.X₃ ≫
        LeftDerivedDelta.LDdelta L n (S.map (U ⋙ V)) (by
          let : PreservesFiniteLimits (U ⋙ V) :=
            preservesFiniteLimits_of_preservesHomology (U ⋙ V)
          let : PreservesFiniteColimits (U ⋙ V) :=
            preservesFiniteColimits_of_preservesHomology (U ⋙ V)
          exact hS.map_of_exact (U ⋙ V)) =
      LeftDerivedDelta.LDdelta ((U ⋙ V) ⋙ L) n S hS ≫
        (leftDerivedPrecompIsoComp U V L n).hom.app S.X₁ := by
  rw [leftDerivedPrecompIsoComp_eq, leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_hom_LDdelta (U ⋙ V) L n S hS

/-- Let `C,D,E,A` be abelian, with projective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving projectives and
homology, and `L : E → A` additive. For short exact `S`, the inverse composite comparisons in
degrees `n+1,n` commute with the connecting maps of `L` on
`(U ⋙ V)(S)` and of `((U ⋙ V) ⋙ L)` on `S`. -/
@[reassoc]
theorem leftDerivedPrecompIsoComp_inv_LDdelta
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (leftDerivedPrecompIsoComp U V L (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta ((U ⋙ V) ⋙ L) n S hS =
      LeftDerivedDelta.LDdelta L n (S.map (U ⋙ V)) (by
          let : PreservesFiniteLimits (U ⋙ V) :=
            preservesFiniteLimits_of_preservesHomology (U ⋙ V)
          let : PreservesFiniteColimits (U ⋙ V) :=
            preservesFiniteColimits_of_preservesHomology (U ⋙ V)
          exact hS.map_of_exact (U ⋙ V)) ≫
        (leftDerivedPrecompIsoComp U V L n).inv.app S.X₁ := by
  rw [leftDerivedPrecompIsoComp_eq, leftDerivedPrecompIsoComp_eq]
  exact leftDerivedPrecompIso_inv_LDdelta (U ⋙ V) L n S hS

end Canonical

section Identity

variable [HasProjectiveResolutions C]

/-- Let `C,A` be abelian, with projective resolutions in `C`, and
`L : C → A` additive. The canonical precomposition comparison for
the identity source functor is the identity isomorphism of `L_nL`. -/
theorem leftDerivedPrecompIso_id (L : C ⥤ A) [L.Additive] (n : ℕ) :
    leftDerivedPrecompIso (𝟭 C) L n = Iso.refl (L.leftDerived n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let e := leftDerivedPrecompIso (𝟭 C) L n
  have hAssoc : (Functor.associator (𝟭 C) (𝟭 C) L).hom = 𝟙 L := by
    apply NatTrans.ext
    funext Y
    rfl
  have h := leftDerivedPrecompIso_inv_comp (𝟭 C) (𝟭 C) L n X
  rw [hAssoc] at h
  have hid := congrArg (fun t => t.app X) (NatTrans.leftDerived_id L n)
  have h' := congrArg (fun t =>
    (leftDerivedPrecompIso (𝟭 C ⋙ 𝟭 C) L n).inv.app X ≫ t) hid
  have hNormalized := h.trans h'
  dsimp only [NatTrans.id_app] at hNormalized
  have hIdem : e.inv.app X ≫ e.inv.app X = e.inv.app X := by
    dsimp only [e, Functor.comp, Functor.id] at hNormalized ⊢
    exact hNormalized.trans (Category.comp_id _)
  have hInv : e.inv.app X = 𝟙 _ := by
    apply (cancel_epi (e.inv.app X)).1
    exact hIdem.trans (Category.comp_id (e.inv.app X)).symm
  have hUnit := e.hom_inv_id_app X
  rw [hInv, Category.comp_id] at hUnit
  exact hUnit

end Identity

section Associativity

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasProjectiveResolutions C] [HasProjectiveResolutions D]
  [HasProjectiveResolutions E] [HasProjectiveResolutions B]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology] [U.PreservesProjectiveObjects]
  (V : D ⥤ E) [V.Additive] [V.PreservesHomology] [V.PreservesProjectiveObjects]
  (W : E ⥤ B) [W.Additive] [W.PreservesHomology] [W.PreservesProjectiveObjects]
  (L : B ⥤ A) [L.Additive]

/-- Let `C,D,E,B,A` be abelian, with projective resolutions in
`C,D,E,B`, and `U : C → D`, `V : D → E`, `W : E → B` additive
and preserving projectives and homology. For additive `L : B → A`,
the comparisons for `U ⋙ (V ⋙ W)` and `(U ⋙ V) ⋙ W` agree under
the derived source associator and the target associator. -/
theorem leftDerivedPrecompIsoComp_assoc (n : ℕ) :
    NatIso.leftDerived (isoWhiskerRight (Functor.associator U V W) L) n ≪≫
        leftDerivedPrecompIsoComp U (V ⋙ W) L n ≪≫
          (isoWhiskerRight (Functor.associator U V W) (L.leftDerived n)).symm =
      leftDerivedPrecompIsoComp (U ⋙ V) W L n := by
  have hSource : isoWhiskerRight (Functor.associator U V W) L =
      Iso.refl (((U ⋙ V) ⋙ W) ⋙ L) := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    change L.map (𝟙 _) = 𝟙 _
    exact L.map_id _
  have hTarget : isoWhiskerRight (Functor.associator U V W) (L.leftDerived n) =
      Iso.refl (((U ⋙ V) ⋙ W) ⋙ L.leftDerived n) := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    change (L.leftDerived n).map (𝟙 _) = 𝟙 _
    exact (L.leftDerived n).map_id _
  rw [hSource, NatIso.leftDerived_refl, hTarget]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom,
    Category.id_comp]
  rw [leftDerivedPrecompIsoComp_eq, leftDerivedPrecompIsoComp_eq]
  simp only [Iso.refl_inv]
  exact Category.comp_id ((leftDerivedPrecompIso (U ⋙ (V ⋙ W)) L n).hom)

end Associativity

section UnitCoherence

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology] [U.PreservesProjectiveObjects]
  (L : D ⥤ A) [L.Additive]

/-- Let `C,D,A` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → A` additive. Inserting the identity of `C` before `U` leaves the composite
precomposition isomorphism equal to the canonical comparison for `U`. -/
theorem leftDerivedPrecompIsoComp_id_left (n : ℕ) :
    leftDerivedPrecompIsoComp (𝟭 C) U L n = leftDerivedPrecompIso U L n :=
  leftDerivedPrecompIsoComp_eq (𝟭 C) U L n

/-- Let `C,D,A` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → A` additive. Inserting the identity of `D` after `U` leaves the composite
precomposition isomorphism equal to the canonical comparison for `U`. -/
theorem leftDerivedPrecompIsoComp_id_right (n : ℕ) :
    leftDerivedPrecompIsoComp U (𝟭 D) L n = leftDerivedPrecompIso U L n :=
  leftDerivedPrecompIsoComp_eq U (𝟭 D) L n

end UnitCoherence

end CategoryTheory.Functor
