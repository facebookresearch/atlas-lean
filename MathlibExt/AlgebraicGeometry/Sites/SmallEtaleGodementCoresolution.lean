/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementAcyclic
public import MathlibExt.CategoryTheory.Monad.Coresolution
public import MathlibExt.CategoryTheory.Monad.AdjunctionCoresolution
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Small étale Godement coresolutions

The point-family adjunction constructs the coaugmented cosimplicial
Godement object. Its terms are skyscraper products and are acyclic for
positive right-derived global sections.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped BigOperators

namespace AlgebraicGeometry.Scheme.DerivedSections

private theorem cosimplicialCoaugmentation_closed.{vC, uC}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    (S : CosimplicialObject.Augmented C) :
    S.hom.app (SimplexCategory.mk 0) ≫ AlternatingCofaceMapComplex.objD S.right 0 = 0 := by
  let A : C := S.left
  let K : CosimplicialObject C := S.right
  let η : A ⟶ K.obj (SimplexCategory.mk 0) := S.hom.app (SimplexCategory.mk 0)
  have h₀ : (𝟙 A) ≫ S.hom.app (SimplexCategory.mk 1) = η ≫ K.δ (0 : Fin 2) :=
    S.hom.naturality (SimplexCategory.δ (0 : Fin 2))
  have h₁ : (𝟙 A) ≫ S.hom.app (SimplexCategory.mk 1) = η ≫ K.δ (1 : Fin 2) :=
    S.hom.naturality (SimplexCategory.δ (1 : Fin 2))
  have he : η ≫ K.δ (0 : Fin 2) = η ≫ K.δ (1 : Fin 2) := h₀.symm.trans h₁
  change η ≫ AlternatingCofaceMapComplex.objD K 0 = 0
  change η ≫ ∑ i : Fin 2, (-1 : ℤ) ^ i.val • K.δ i = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, Preadditive.comp_add, Preadditive.comp_neg]
  rw [he]
  exact add_neg_cancel _

private theorem shortComplexExact_of_contraction.{vC, uC}
    {C : Type uC} [Category.{vC} C] [Abelian C] (S : ShortComplex C)
    (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂)
    (h : r ≫ S.f + S.g ≫ s = 𝟙 S.X₂) : S.Exact := by
  have hi : (S.iCycles ≫ r) ≫ S.f = S.iCycles := by
    have hh := congrArg (fun f : S.X₂ ⟶ S.X₂ => S.iCycles ≫ f) h
    simpa only [Preadditive.comp_add, ← Category.assoc, S.iCycles_g,
      zero_comp, add_zero, Category.comp_id] using hh
  have ht : (S.iCycles ≫ r) ≫ S.toCycles = 𝟙 S.cycles := by
    apply (cancel_mono S.iCycles).1
    simpa only [Category.assoc, S.toCycles_i, Category.id_comp] using hi
  let : IsSplitEpi S.toCycles :=
    IsSplitEpi.mk' { section_ := S.iCycles ≫ r, id := ht }
  exact (S.exact_iff_epi_toCycles).mpr inferInstance

private theorem shortComplexExact_of_coordinateContraction.{vC, uC}
    {C : Type uC} [Category.{vC} C] [Abelian C] (S : ShortComplex C)
    {A B D : C} (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ D)
    (f : A ⟶ B) (g : B ⟶ D)
    (hf : S.f ≫ e₂.hom = e₁.hom ≫ f) (hg : S.g ≫ e₃.hom = e₂.hom ≫ g)
    (r : B ⟶ A) (s : D ⟶ B) (h : r ≫ f + g ≫ s = 𝟙 B) : S.Exact := by
  have hz : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).1
    calc
      e₁.hom ≫ (f ≫ g) = (S.f ≫ e₂.hom) ≫ g := by rw [← Category.assoc, ← hf]
      _ = S.f ≫ (S.g ≫ e₃.hom) := by rw [Category.assoc, ← hg]
      _ = 0 := by rw [← Category.assoc, S.zero, zero_comp]
      _ = e₁.hom ≫ 0 := comp_zero.symm
  let S' := ShortComplex.mk f g hz
  let e : S ≅ S' := ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm
  exact ShortComplex.exact_of_iso e.symm (shortComplexExact_of_contraction S' r s h)

private theorem coresolutionMappedDifferential.{vC, uC, vD, uD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (L : C ⥤ D) [L.Additive] (T : Monad C) (Q : C) (n : ℕ) :
    L.map ((AlternatingCofaceMapComplex.obj (Monad.coresolution T Q)).d n (n + 1)) ≫
        L.map (Monad.coresolutionObjIso T Q (n + 1)).hom =
      L.map (Monad.coresolutionObjIso T Q n).hom ≫
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          L.map (Monad.barEtaAtPos T (n + 1) i Q) := by
  let K := Monad.coresolution T Q
  let e := fun j : ℕ => Monad.coresolutionObjIso T Q j
  have hd : (AlternatingCofaceMapComplex.obj K).d n (n + 1) =
      AlternatingCofaceMapComplex.objD K n := by
    dsimp only [AlternatingCofaceMapComplex.obj]
    exact CochainComplex.of_d _ _ n
  rw [hd]
  let a := fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • K.δ i
  have hm : L.map (∑ i, a i) = ∑ i, L.map (a i) :=
    _root_.map_sum
      (L.mapAddHom : (K.obj (SimplexCategory.mk n) ⟶ K.obj (SimplexCategory.mk (n + 1))) →+
        (L.obj (K.obj (SimplexCategory.mk n)) ⟶ L.obj (K.obj (SimplexCategory.mk (n + 1)))))
      a Finset.univ
  change L.map (∑ i, a i) ≫ L.map (e (n + 1)).hom = _
  rw [hm, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  change L.map ((-1 : ℤ) ^ i.val • K.δ i) ≫ L.map (e (n + 1)).hom = _
  rw [L.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  exact congrArg (fun f => (-1 : ℤ) ^ i.val • f)
    ((L.map_comp (K.δ i) (e (n + 1)).hom).symm.trans
      ((congrArg L.map (Monad.coresolutionObjIso_coface T Q i)).trans
        (L.map_comp (e n).hom (Monad.barEtaAtPos T (n + 1) i Q))))

/-- The genuine coaugmented Godement cosimplicial object on the original sheaf category. -/
def smallEtaleGodementAugmentedCoresolution (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialObject.Augmented (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  Monad.coresolutionAugmented (smallEtaleGodementMonad.{u, w} X) Q

/-- The underlying actual Godement cosimplicial object. -/
def smallEtaleGodementCoresolution (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialObject (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  Monad.coresolution (smallEtaleGodementMonad.{u, w} X) Q

/-- Every actual Godement degree is the original skyscraper product of an iterated stalk family. -/
def smallEtaleGodementCoresolutionTermIso (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (smallEtaleGodementCoresolution.{u, w} X Q).obj (SimplexCategory.mk n) ≅
      (smallEtaleGodementSkyscrapers.{u, w} X).obj
        ((smallEtaleGodementStalks.{u, w} X).obj
          ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).obj Q)) :=
  Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} X) Q n ≪≫
    eqToIso (Monad.monadPow_succ_obj_eq (smallEtaleGodementMonad.{u, w} X) n Q)

/-- The degree-zero coaugmentation is the same original geometric-germ Godement unit. -/
theorem smallEtaleGodementAugmentedCoresolution_unit (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementAugmentedCoresolution.{u, w} X Q).hom.app (SimplexCategory.mk 0) =
      (smallEtaleGodementUnit.{u, w} X).app Q := by
  exact Monad.coresolutionAugmented_hom_zero (smallEtaleGodementMonad.{u, w} X) Q

/-- Every positive right-derived global-section object of every actual degree term is zero. -/
theorem smallEtaleGodementCoresolutionTerm_derivedSections_succ_isZero (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n i : ℕ) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived (i + 1)).obj
      ((smallEtaleGodementCoresolution.{u, w} X Q).obj (SimplexCategory.mk n))) := by
  let T := smallEtaleGodementMonad.{u, w} X
  let M := (smallEtaleGodementStalks.{u, w} X).obj ((Monad.monadPow T n).obj Q)
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  exact IsZero.of_iso (smallEtaleGodementDerivedSections_succ_isZero.{u, w} X M i)
    ((Γ.rightDerived (i + 1)).mapIso (smallEtaleGodementCoresolutionTermIso.{u, w} X Q n))

/-- The actual alternating-coface Godement cochain complex on the original sheaf category. -/
def smallEtaleGodementCochainComplex (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) ℕ :=
  (alternatingCofaceMapComplex _).obj (smallEtaleGodementCoresolution.{u, w} X Q)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original Godement unit is closed for the actual first alternating differential. -/
theorem smallEtaleGodementUnit_d_zero (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementUnit.{u, w} X).app Q ≫
      (smallEtaleGodementCochainComplex.{u, w} X Q).d 0 1 = 0 := by
  rw [← smallEtaleGodementAugmentedCoresolution_unit]
  let S := smallEtaleGodementAugmentedCoresolution.{u, w} X Q
  change S.hom.app (SimplexCategory.mk 0) ≫
    (AlternatingCofaceMapComplex.obj S.right).d 0 1 = 0
  change S.hom.app (SimplexCategory.mk 0) ≫ AlternatingCofaceMapComplex.objD S.right 0 = 0
  exact cosimplicialCoaugmentation_closed S

/-- The original unit supplies the actual cochain coaugmentation from the original sheaf. -/
def smallEtaleGodementCochainCoaugmentation (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (CochainComplex.single₀ _).obj Q ⟶ smallEtaleGodementCochainComplex.{u, w} X Q :=
  (CochainComplex.fromSingle₀Equiv (smallEtaleGodementCochainComplex.{u, w} X Q) Q).symm
    ⟨(smallEtaleGodementUnit.{u, w} X).app Q, smallEtaleGodementUnit_d_zero.{u, w} X Q⟩

/-- The degree-zero cochain map is the literal original Godement unit. -/
theorem smallEtaleGodementCochainCoaugmentation_f_zero (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementCochainCoaugmentation.{u, w} X Q).f 0 =
      (smallEtaleGodementUnit.{u, w} X).app Q :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Actual stalk-family degree coordinates are the same canonical monad-power coordinates. -/
def smallEtaleGodementStalkDegreeIso (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (smallEtaleGodementStalks.{u, w} X).obj
        ((smallEtaleGodementCochainComplex.{u, w} X Q).X n) ≅
      (smallEtaleGodementStalks.{u, w} X).obj
        ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) (n + 1)).obj Q) :=
  (smallEtaleGodementStalks.{u, w} X).mapIso
    (Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} X) Q n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual stalk differential is the alternating original unit insertion in degree
coordinates. -/
theorem smallEtaleGodementStalkDegreeIso_d (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (smallEtaleGodementStalks.{u, w} X).map
        ((smallEtaleGodementCochainComplex.{u, w} X Q).d n (n + 1)) ≫
      (smallEtaleGodementStalkDegreeIso.{u, w} X Q (n + 1)).hom =
        (smallEtaleGodementStalkDegreeIso.{u, w} X Q n).hom ≫
          ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
            (smallEtaleGodementStalks.{u, w} X).map
              (Monad.barEtaAtPos (smallEtaleGodementMonad.{u, w} X) (n + 1) i Q) := by
  exact coresolutionMappedDifferential (smallEtaleGodementStalks.{u, w} X)
    (smallEtaleGodementMonad.{u, w} X) Q n

set_option backward.isDefEq.respectTransparency.types false in
private theorem godementStalkShortComplexExact (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (((smallEtaleGodementCochainComplex.{u, w} X Q).sc (n + 1)).map
      (smallEtaleGodementStalks.{u, w} X)).Exact := by
  let L := smallEtaleGodementStalks.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let T := adj.toMonad
  let e := fun j : ℕ => smallEtaleGodementStalkDegreeIso.{u, w} X Q j
  let d := fun j : ℕ => ∑ i : Fin (j + 2), (-1 : ℤ) ^ i.val •
    L.map (Monad.barEtaAtPos T (j + 1) i Q)
  let r := fun j : ℕ => Monad.adjunctionCoresolutionRetraction adj j Q
  let K := smallEtaleGodementCochainComplex.{u, w} X Q
  let S := (K.sc' n (n + 1) (n + 2)).map L
  have hf : S.f ≫ (e (n + 1)).hom = (e n).hom ≫ d n :=
    smallEtaleGodementStalkDegreeIso_d.{u, w} X Q n
  have hg : S.g ≫ (e (n + 2)).hom = (e (n + 1)).hom ≫ d (n + 1) :=
    smallEtaleGodementStalkDegreeIso_d.{u, w} X Q (n + 1)
  have hc : r (n + 1) ≫ d n + d (n + 1) ≫ r (n + 2) = 𝟙 _ := by
    dsimp only [r, d, T, L, adj]
    have h := Monad.adjunctionCoresolutionRetraction_alternating adj (n + 1) Q
    exact (add_comm _ _).trans h
  have hs : S.Exact := shortComplexExact_of_coordinateContraction S (e n) (e (n + 1))
    (e (n + 2)) (d n) (d (n + 1)) hf hg (r (n + 1)) (r (n + 2)) hc
  let ei := K.isoSc' n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
    (CochainComplex.next ℕ (n + 1))
  exact ShortComplex.exact_of_iso (L.mapShortComplex.mapIso ei).symm hs

set_option backward.isDefEq.respectTransparency.types false in
private theorem godementStalks_reflectExact (X : Scheme.{u})
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : (S.map (smallEtaleGodementStalks.{u, w} X)).Exact) : S.Exact := by
  let L := smallEtaleGodementStalks.{u, w} X
  have hP :=
    (smallEtaleCanonicalGeometricPointsCommon_conservative.{u, w} X).jointlyReflectIsomorphisms
      AddCommGrpCat.{max u w}
  apply (hP.exact_iff S).mpr
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
  subst Φ
  let E := (piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor
  let V := (CategoryTheory.evaluation (Discrete X) AddCommGrpCat.{max u w}).obj ⟨x⟩
  let : E.Additive :=
    (piEquivalenceFunctorDiscrete X
        AddCommGrpCat.{max u w}).fullyFaithfulFunctor.additive_ofFullyFaithful
  have hEV : (((S.map L).map E).map V).Exact := (hS.map E).map V
  let : (CategoryTheory.Pi.eval (fun _ : X => AddCommGrpCat.{max u w}) x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso
      (piEquivalenceFunctorDiscreteCompEvaluationIso AddCommGrpCat.{max u w} x)
  let e := (S.map L).mapNatIso
    (piEquivalenceFunctorDiscreteCompEvaluationIso AddCommGrpCat.{max u w} x)
  exact ShortComplex.exact_of_iso e hEV

/-- The actual Godement cochain complex is exact in every positive degree. -/
theorem smallEtaleGodementCochainComplex_exactAt_succ (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    (smallEtaleGodementCochainComplex.{u, w} X Q).ExactAt (n + 1) :=
  godementStalks_reflectExact.{u, w} X _ (godementStalkShortComplexExact.{u, w} X Q n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original unit and first Godement differential form the actual exact augmentation row. -/
theorem smallEtaleGodementCochainCoaugmentation_exact (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (ShortComplex.mk ((smallEtaleGodementUnit.{u, w} X).app Q)
      ((smallEtaleGodementCochainComplex.{u, w} X Q).d 0 1)
      (smallEtaleGodementUnit_d_zero.{u, w} X Q)).Exact := by
  let K := smallEtaleGodementCochainComplex.{u, w} X Q
  let S := ShortComplex.mk ((smallEtaleGodementUnit.{u, w} X).app Q)
    (K.d 0 1) (smallEtaleGodementUnit_d_zero.{u, w} X Q)
  apply godementStalks_reflectExact.{u, w} X S
  let L := smallEtaleGodementStalks.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let T := adj.toMonad
  let e := fun j : ℕ => smallEtaleGodementStalkDegreeIso.{u, w} X Q j
  let f := L.map (Monad.barEtaAtPos T 0 0 Q)
  let g := ∑ i : Fin 2, (-1 : ℤ) ^ i.val • L.map (Monad.barEtaAtPos T 1 i Q)
  let r := Monad.adjunctionCoresolutionRetraction adj 0 Q
  let s := Monad.adjunctionCoresolutionRetraction adj 1 Q
  have hf : (S.map L).f ≫ (e 0).hom = (Iso.refl (L.obj Q)).hom ≫ f := by
    change L.map ((smallEtaleGodementUnit.{u, w} X).app Q) ≫
      L.map (Monad.coresolutionObjIso T Q 0).hom = (𝟙 _) ≫ f
    rw [Category.id_comp, Monad.coresolutionObjIso_hom]
    change L.map (T.η.app Q) ≫ L.map (𝟙 _) = L.map (T.η.app Q)
    rw [L.map_id]
    exact Category.comp_id _
  have hg : (S.map L).g ≫ (e 1).hom = (e 0).hom ≫ g :=
    smallEtaleGodementStalkDegreeIso_d.{u, w} X Q 0
  have hc : r ≫ f + g ≫ s = 𝟙 _ := by
    have h : g ≫ s + r ≫
        (∑ i : Fin 1, (-1 : ℤ) ^ i.val • L.map (Monad.barEtaAtPos T 0 i Q)) = 𝟙 _ :=
      Monad.adjunctionCoresolutionRetraction_alternating adj 0 Q
    rw [Fin.sum_univ_one] at h
    change g ≫ s + r ≫ ((1 : ℤ) • f) = 𝟙 _ at h
    rw [one_zsmul] at h
    exact (add_comm _ _).trans h
  exact shortComplexExact_of_coordinateContraction (S.map L) (Iso.refl (L.obj Q))
    (e 0) (e 1) f g hf hg r s hc

set_option backward.isDefEq.respectTransparency.types false in
private theorem cochainCoaugmentation_quasiIsoAt_zero.{vC, uC}
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {Q : C} (K : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj Q ⟶ K)
    (h : (ShortComplex.mk (ι.f 0) (K.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact)
    [Mono (ι.f 0)] : QuasiIsoAt ι 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  apply (ShortComplex.quasiIso_iff_of_zeros _
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 Q 0 0)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 Q 0 1)
    (K.shape 0 0 (by simp [ComplexShape.up_Rel]))).mpr
  refine ⟨h, ?_⟩
  change Mono (ι.f 0)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal original unit coaugmentation is a quasi-isomorphism. -/
theorem smallEtaleGodementCochainCoaugmentation_quasiIso (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    QuasiIso (smallEtaleGodementCochainCoaugmentation.{u, w} X Q) := by
  let K := smallEtaleGodementCochainComplex.{u, w} X Q
  let ι := smallEtaleGodementCochainCoaugmentation.{u, w} X Q
  apply (_root_.quasiIso_iff ι).mpr
  intro n
  cases n with
  | zero =>
      have hm : Mono (ι.f 0) := by
        rw [smallEtaleGodementCochainCoaugmentation_f_zero]
        exact smallEtaleGodementUnit_mono.{u, w} X Q
      let : Mono (ι.f 0) := hm
      apply cochainCoaugmentation_quasiIsoAt_zero K ι
      let S₁ := ShortComplex.mk (ι.f 0) (K.d 0 1)
        (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])
      let S₂ := ShortComplex.mk ((smallEtaleGodementUnit.{u, w} X).app Q)
        (K.d 0 1) (smallEtaleGodementUnit_d_zero.{u, w} X Q)
      let e : S₁ ≅ S₂ := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          change (𝟙 Q) ≫ (smallEtaleGodementUnit.{u, w} X).app Q =
            ι.f 0 ≫ (𝟙 (K.X 0))
          rw [Category.id_comp, Category.comp_id]
          exact (smallEtaleGodementCochainCoaugmentation_f_zero.{u, w} X Q).symm)
        (by
          change (𝟙 (K.X 0)) ≫ K.d 0 1 = K.d 0 1 ≫ (𝟙 (K.X 1))
          rw [Category.id_comp, Category.comp_id])
      exact ShortComplex.exact_of_iso e.symm
        (smallEtaleGodementCochainCoaugmentation_exact.{u, w} X Q)
  | succ n =>
      exact (quasiIsoAt_iff_exactAt ι (n + 1)
        (CochainComplex.exactAt_succ_single_obj Q n)).mpr
          (smallEtaleGodementCochainComplex_exactAt_succ.{u, w} X Q n)

end AlgebraicGeometry.Scheme.DerivedSections
