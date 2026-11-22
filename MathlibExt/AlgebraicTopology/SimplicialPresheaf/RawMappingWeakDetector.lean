/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveDerivedMappingComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-!
# Original raw mapping weak detection

The actual scalar cylinder gives component-to-canonical-Ho soundness on the
original presheaf category. Two original chosen fibrant targets then detect
the actual base weak class, without a monicity condition on the tested map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen MonoidalClosed

attribute [local instance] SimplicialPresheaf.scalarEnrichment
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The original scalar cylinder's pointwise first projection. -/
private def scalarIntervalProjection (A : SimplicialPresheaf.{u} D) :
    (scalarTensor.obj A).obj (Δ[1] : SSet.{u}) ⟶ A where
  app d := fst (A.obj d) (Δ[1] : SSet.{u})
  naturality := by intro d e f; ext n x; rfl

/-- The original scalar interval starts at the actual vertex-zero inclusion. -/
private def scalarIntervalZero (A : SimplicialPresheaf.{u} D) :
    A ⟶ (scalarTensor.obj A).obj (Δ[1] : SSet.{u}) where
  app d := SSet.ι₀
  naturality := by intro d e f; ext n x; rfl

/-- The original scalar interval ends at the actual vertex-one inclusion. -/
private def scalarIntervalOne (A : SimplicialPresheaf.{u} D) :
    A ⟶ (scalarTensor.obj A).obj (Δ[1] : SSet.{u}) where
  app d := SSet.ι₁
  naturality := by intro d e f; ext n x; rfl

/-- Every actual scalar component of the interval projection is weak, for any source. -/
private theorem scalarIntervalProjection_weak (A : SimplicialPresheaf.{u} D) :
    weakEquivalences (SimplicialPresheaf.{u} D) (scalarIntervalProjection A) := by
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences
    (scalarIntervalProjection A)
  rw [(data D).weakEquivalences_eq]
  intro d
  change SSet.realizationWeakEquivalences
    ((SSet.modelCategoryQuillen.standardCylinder (A.obj d)).π)
  exact (weakEquivalence_iff _).mp
      ((SSet.modelCategoryQuillen.standardCylinder (A.obj d)).weakEquivalence_π)

/-- The actual original cylinder has both original endpoints and its constructed weak projection. -/
private def scalarCylinder (A : SimplicialPresheaf.{u} D) : Cylinder A where
  I := (scalarTensor.obj A).obj (Δ[1] : SSet.{u})
  i₀ := scalarIntervalZero A
  i₁ := scalarIntervalOne A
  π := scalarIntervalProjection A
  i₀_π := by ext d n x; rfl
  i₁_π := by ext d n x; rfl
  weakEquivalence_π := (weakEquivalence_iff _).mpr (scalarIntervalProjection_weak A)

/-- Every original degree of the standard zero simplex has its unique original point. -/
private theorem zeroPoint_eq {n : SimplexCategoryᵒᵖ}
    (x y : (Δ[0] : SSet.{u}).obj n) : x = y := by
  apply SSet.stdSimplex.objEquiv.injective
  ext a : 3
  change (_ : Fin 1) = _
  exact Subsingleton.elim _ _

/-- The scalar zero-simplex tensor uses its actual terminal comparison to the original object. -/
private def scalarZeroIso (A : SimplicialPresheaf.{u} D) :
    (scalarTensor.obj A).obj (Δ[0] : SSet.{u}) ≅ A where
  hom :=
    { app := fun d => fst (A.obj d) (Δ[0] : SSet.{u})
      naturality := by intro d e f; ext n x; rfl }
  inv :=
    { app := fun d => lift (𝟙 (A.obj d)) (SSet.stdSimplex.isTerminalObj₀.from (A.obj d))
      naturality := by
        intro d e f
        ext n x
        apply Prod.ext
        · rfl
        · exact zeroPoint_eq _ _ }
  hom_inv_id := by
    ext d n x
    apply Prod.ext
    · rfl
    · exact zeroPoint_eq _ _
  inv_hom_id := by ext d n x; rfl

/-- The actual standard zero simplex maps to the native scalar tensor unit. -/
private def zeroToUnit : (Δ[0] : SSet.{u}) ⟶ (𝟙_ SSet.{u}) where
  app _ := ↾fun _ => PUnit.unit
  naturality := by intro d e f; ext x; rfl

/-- Ordinary unit-point conversion preserves the actual standard-simplex Yoneda map. -/
private theorem zero_unit_yoneda {K : SSet.{u}} (f : (𝟙_ SSet.{u}) ⟶ K) :
    SSet.yonedaEquiv.symm (SSet.unitHomEquiv K f) = zeroToUnit ≫ f := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The original end's zero-simplex transposition uses the actual scalar zero-unit map. -/
private theorem zeroSimplexTransposition (A Z : SimplicialPresheaf.{u} D) (g : A ⟶ Z) :
    innerHomSimplexEquiv A Z (op ⦋0⦌) (innerHomHomEquiv A Z g) =
      (scalarZeroIso A).hom ≫ g := by
  apply (scalarTensorHomEquiv A (Δ[0] : SSet.{u}) Z).injective
  simp only [innerHomSimplexEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [innerHomHomEquiv, Equiv.trans_apply, zero_unit_yoneda]
  apply innerHom_ext
  intro d
  rw [scalarTensorHomEquiv_π, Category.assoc]
  rw [innerHomπ, Enriched.FunctorCategory.homEquiv_apply_π,
    CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv]
  unfold CategoryTheory.MonoidalClosed.curry'
  rw [← CategoryTheory.MonoidalClosed.curry_natural_left]
  congr 1

/-- Every original zero simplex is transposed using the same actual unit map. -/
private theorem zeroSimplexInverse (A Z : SimplicialPresheaf.{u} D)
    (x : (innerHom A Z).obj (op ⦋0⦌)) :
    innerHomSimplexEquiv A Z (op ⦋0⦌) x =
      (scalarZeroIso A).hom ≫ (innerHomHomEquiv A Z).symm x := by
  simpa only [Equiv.apply_symm_apply] using
    zeroSimplexTransposition A Z ((innerHomHomEquiv A Z).symm x)

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The original first interval endpoint is the actual scalar delta-one map. -/
private theorem scalarEndpointZeroFactor (A : SimplicialPresheaf.{u} D) :
    scalarIntervalZero A = (scalarZeroIso A).inv ≫
      (scalarTensor.obj A).map (SSet.stdSimplex.δ (1 : Fin 2)) := by
  ext d n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    rfl

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The original last interval endpoint is the actual scalar delta-zero map. -/
private theorem scalarEndpointOneFactor (A : SimplicialPresheaf.{u} D) :
    scalarIntervalOne A = (scalarZeroIso A).inv ≫
      (scalarTensor.obj A).map (SSet.stdSimplex.δ (0 : Fin 2)) := by
  ext d n x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    rfl

/-- An actual raw end edge gives a full original cylinder homotopy with both ordered endpoints. -/
private def rawEdgeLeftHomotopy (A Z : SimplicialPresheaf.{u} D)
    {x y : (innerHom A Z).obj (op ⦋0⦌)} (e : (innerHom A Z).Edge x y) :
    (scalarCylinder A).LeftHomotopy ((innerHomHomEquiv A Z).symm x)
      ((innerHomHomEquiv A Z).symm y) where
  h := innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge
  h₀ := by
    change scalarIntervalZero A ≫ innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge = _
    rw [scalarEndpointZeroFactor, Category.assoc]
    have ht := innerHomSimplexEquiv_operator A Z (SimplexCategory.δ (1 : Fin 2)).op e.edge
    change innerHomSimplexEquiv A Z (op ⦋0⦌) ((innerHom A Z).δ (1 : Fin 2) e.edge) =
      (scalarTensor.obj A).map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
        innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge at ht
    rw [e.src_eq] at ht
    rw [← ht, zeroSimplexInverse, ← Category.assoc,
      (scalarZeroIso A).inv_hom_id, Category.id_comp]
  h₁ := by
    change scalarIntervalOne A ≫ innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge = _
    rw [scalarEndpointOneFactor, Category.assoc]
    have ht := innerHomSimplexEquiv_operator A Z (SimplexCategory.δ (0 : Fin 2)).op e.edge
    change innerHomSimplexEquiv A Z (op ⦋0⦌) ((innerHom A Z).δ (0 : Fin 2) e.edge) =
      (scalarTensor.obj A).map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
        innerHomSimplexEquiv A Z (op ⦋1⦌) e.edge at ht
    rw [e.tgt_eq] at ht
    rw [← ht, zeroSimplexInverse, ← Category.assoc,
      (scalarZeroIso A).inv_hom_id, Category.id_comp]

/-- Every actual raw end edge has equal images in the original canonical model localization. -/
private theorem rawEdgeEqualized (A Z : SimplicialPresheaf.{u} D)
    {x y : (innerHom A Z).obj (op ⦋0⦌)} (e : (innerHom A Z).Edge x y) :
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).map ((innerHomHomEquiv A Z).symm x) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map ((innerHomHomEquiv A Z).symm y) := by
  have h := (rawEdgeLeftHomotopy A Z e).leftHomotopyRel
  exact h.factorsThroughLocalization.map_eq _

/-- The actual raw component quotient maps soundly to the original canonical Ho Hom. -/
private def rawComponentToHo (A Z : SimplicialPresheaf.{u} D) :
    SSet.π₀ (innerHom A Z) →
      ((toHomotopyCategory (SimplicialPresheaf.{u} D)).obj A ⟶
        (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj Z) :=
  SSet.π₀.lift (fun x =>
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).map ((innerHomHomEquiv A Z).symm x))
      (fun {x y} e => rawEdgeEqualized A Z (x := x) (y := y) e)

/-- Equality of original raw components implies equality of their canonical Ho maps. -/
private theorem rawComponents_sound {A Z : SimplicialPresheaf.{u} D} (g h : A ⟶ Z)
    (e : SSet.π₀.mk (innerHomHomEquiv A Z g) = SSet.π₀.mk (innerHomHomEquiv A Z h)) :
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).map g =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map h := by
  have he := congrArg (rawComponentToHo A Z) e
  simpa only [rawComponentToHo, SSet.π₀.lift_mk, Equiv.symm_apply_apply] using he

/-- Actual original fibrancy of the target produces the raw mapping object's Kan structure. -/
private theorem rawMappingKan (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.KanComplex (innerHom A Z) :=
  innerHom_isFibrant A Z hZ

/-- Full scalar weakness between the actual raw Kan objects preserves their original components. -/
private theorem weakRawKan_bijectiveπ₀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f) :
    Function.Bijective (SSet.mapπ₀ f) :=
  (SSet.KanComplex.W_iff_realizationWeakEquivalence f).mpr hf |>.bijective_mapπ₀

/-- The two actual replacement-target tests give both inverse equations in canonical Ho. -/
private theorem weak_of_twoRawTargets {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hA : SSet.realizationWeakEquivalences (innerHomPre f ((originalR D).obj A)))
    (hB : SSet.realizationWeakEquivalences (innerHomPre f ((originalR D).obj B))) :
    weakEquivalences (SimplicialPresheaf.{u} D) f := by
  let RA := (originalR D).obj A
  let RB := (originalR D).obj B
  let ηA : A ⟶ RA := (originalRUnit D).app A
  let ηB : B ⟶ RB := (originalRUnit D).app B
  let Rf : RA ⟶ RB := (originalR D).map f
  let : SSet.KanComplex (innerHom A RA) := rawMappingKan A RA (originalR_isFibrant A)
  let : SSet.KanComplex (innerHom B RA) := rawMappingKan B RA (originalR_isFibrant A)
  let : SSet.KanComplex (innerHom A RB) := rawMappingKan A RB (originalR_isFibrant B)
  let : SSet.KanComplex (innerHom B RB) := rawMappingKan B RB (originalR_isFibrant B)
  have bijA := weakRawKan_bijectiveπ₀ (innerHomPre f RA) hA
  have bijB := weakRawKan_bijectiveπ₀ (innerHomPre f RB) hB
  obtain ⟨q, hq⟩ := bijA.2 (SSet.π₀.mk (innerHomHomEquiv A RA ηA))
  obtain ⟨x, hx⟩ := SSet.π₀.mk_surjective q
  let g : B ⟶ RA := (innerHomHomEquiv B RA).symm x
  have hgx : innerHomHomEquiv B RA g = x := Equiv.apply_symm_apply _ _
  have hFirst : SSet.π₀.mk (innerHomHomEquiv A RA (f ≫ g)) =
      SSet.π₀.mk (innerHomHomEquiv A RA ηA) := by
    rw [← hx, SSet.mapπ₀_mk, ← hgx, innerHomHomEquiv_precomp] at hq
    exact hq
  have hPost : SSet.π₀.mk (innerHomHomEquiv A RB (f ≫ g ≫ Rf)) =
      SSet.π₀.mk (innerHomHomEquiv A RB (f ≫ ηB)) := by
    have hp := congrArg (SSet.mapπ₀ (innerHomPost A Rf)) hFirst
    simp only [SSet.mapπ₀_mk, innerHomHomEquiv_postcomp] at hp
    have hη : f ≫ ηB = ηA ≫ Rf := (originalReplacement_naturality f).2
    rw [← hη] at hp
    simpa only [Category.assoc] using hp
  have hSecond : SSet.π₀.mk (innerHomHomEquiv B RB (g ≫ Rf)) =
      SSet.π₀.mk (innerHomHomEquiv B RB ηB) := by
    apply bijB.1
    simp only [SSet.mapπ₀_mk, innerHomHomEquiv_precomp]
    exact hPost
  let L := toHomotopyCategory (SimplicialPresheaf.{u} D)
  have hfg : L.map f ≫ L.map g = L.map ηA := by
    simpa only [L, Functor.map_comp] using rawComponents_sound (f ≫ g) ηA hFirst
  have hgR : L.map g ≫ L.map Rf = L.map ηB := by
    simpa only [L, Functor.map_comp] using rawComponents_sound (g ≫ Rf) ηB hSecond
  have hIsoA : IsIso (L.map ηA) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map ηA).mp
      (originalRUnit_trivialCofibration A).2
  have hIsoB : IsIso (L.map ηB) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map ηB).mp
      (originalRUnit_trivialCofibration B).2
  let : IsIso (L.map ηA) := hIsoA
  let : IsIso (L.map ηB) := hIsoB
  let k : L.obj B ⟶ L.obj A := L.map g ≫ inv (L.map ηA)
  have hkLeft : L.map f ≫ k = 𝟙 (L.obj A) := by
    dsimp only [k]
    rw [← Category.assoc, hfg]
    exact IsIso.hom_inv_id _
  have hnat : L.map f ≫ L.map ηB = L.map ηA ≫ L.map Rf := by
    rw [← L.map_comp, ← L.map_comp]
    exact L.congr_map (show f ≫ ηB = ηA ≫ Rf from (originalReplacement_naturality f).2)
  have hinv : inv (L.map ηA) ≫ L.map f = L.map Rf ≫ inv (L.map ηB) := by
    apply (cancel_mono (L.map ηB)).mp
    calc
      (inv (L.map ηA) ≫ L.map f) ≫ L.map ηB =
          inv (L.map ηA) ≫ (L.map f ≫ L.map ηB) := Category.assoc _ _ _
      _ = inv (L.map ηA) ≫ (L.map ηA ≫ L.map Rf) :=
        congrArg (fun h => inv (L.map ηA) ≫ h) hnat
      _ = L.map Rf := by rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = (L.map Rf ≫ inv (L.map ηB)) ≫ L.map ηB := by
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hkRight : k ≫ L.map f = 𝟙 (L.obj B) := by
    dsimp only [k]
    rw [Category.assoc, hinv, ← Category.assoc, hgR]
    exact IsIso.hom_inv_id _
  have hfIso : IsIso (L.map f) := ⟨⟨k, hkLeft, hkRight⟩⟩
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).mpr hfIso

/-- The actual original weak class is detected by the two SAME chosen fibrant replacement
targets. -/
theorem weakEquivalence_iff_rawPrecomp_twoReplacementTargets
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) :
    weakEquivalences (SimplicialPresheaf.{u} D) f ↔
      SSet.realizationWeakEquivalences (innerHomPre f ((originalR D).obj A)) ∧
        SSet.realizationWeakEquivalences (innerHomPre f ((originalR D).obj B)) := by
  constructor
  · intro hf
    exact ⟨innerHomPre_weak_of_weakEquivalence f ((originalR D).obj A) hf
        (originalR_isFibrant A),
      innerHomPre_weak_of_weakEquivalence f ((originalR D).obj B) hf
        (originalR_isFibrant B)⟩
  · rintro ⟨hA, hB⟩
    exact weak_of_twoRawTargets f hA hB

/-- Every original arrow is weak exactly when all actual fibrant raw targets see it as weak. -/
theorem weakEquivalence_iff_rawPrecomp_all_fibrant
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) :
    weakEquivalences (SimplicialPresheaf.{u} D) f ↔
      ∀ Z : SimplicialPresheaf.{u} D, IsFibrant Z →
        SSet.realizationWeakEquivalences (innerHomPre f Z) := by
  constructor
  · intro hf Z hZ
    exact innerHomPre_weak_of_weakEquivalence f Z hf hZ
  · intro h
    exact (weakEquivalence_iff_rawPrecomp_twoReplacementTargets f).mpr
      ⟨h ((originalR D).obj A) (originalR_isFibrant A),
        h ((originalR D).obj B) (originalR_isFibrant B)⟩

end SimplicialPresheaf.InjectiveKan
