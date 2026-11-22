/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
public import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalarsCoherence

/-!
# Actual Quillen and derived scalar change for internal modules

The full created module models make the original balanced scalar adjunction
Quillen: restriction preserves the entire underlying arrow, and therefore
creates both weak equivalences and fibrations. No weak-equivalence or flatness
assumption on the scalar map is needed for this adjunction.

The construction uses the source maps of Schwede--Shipley's module comparison
proof and EKMM, Chapter III, §4. Weak scalar equivalences and the additional
relative-flatness criterion for an equivalence remain separate assertions.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty Functor
open scoped CategoryTheory.MonObj
open CategoryTheory.Mod.ExtensionOfScalars
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.ModuleTransfer.ScalarChange

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  {A B : C} [MonObj A] [MonObj B]

section CreatedModels

variable
  [ModelCategory (Mod C A)] [ModelCategory (Mod C B)]

/-- Restriction creates the whole original weak class in the two created module models. -/
theorem restrictionCreatesWeakEquivalences
    (hA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] :
    weakEquivalences (Mod C B) = (weakEquivalences (Mod C A)).inverseImage (restriction p) := by
  rw [hA, hB]
  rfl

/-- The full original underlying fibrations are created by actual scalar restriction. -/
theorem restrictionCreatesFibrations
    (hA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] :
    fibrations (Mod C B) = (fibrations (Mod C A)).inverseImage (restriction p) := by
  rw [hA, hB]
  rfl

/-- The same whole-arrow restriction creates the complete trivial-fibration class. -/
theorem restrictionCreatesTrivialFibrations
    (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] :
    trivialFibrations (Mod C B) = (trivialFibrations (Mod C A)).inverseImage (restriction p) := by
  change fibrations (Mod C B) ⊓ weakEquivalences (Mod C B) = _
  rw [restrictionCreatesFibrations hFA hFB p, restrictionCreatesWeakEquivalences hWA hWB p]
  rfl

/-- The actual balanced extension/restriction adjunction is Quillen for the full created models. -/
theorem isQuillen
    (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))
    (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)] :
    (adjunction p).IsQuillenAdjunction :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (restrictionCreatesFibrations hFA hFB p).le
    (restrictionCreatesTrivialFibrations hWA hWB hFA hFB p).le

section Derived

variable
  (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
  (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
  (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
  (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))

/-- The original restriction already preserves every weak map, so its localization is a right derived functor. -/
def rightDerived (p : A ⟶ B) [IsMonHom p] :
    (weakEquivalences (Mod C B)).Localization ⥤ (weakEquivalences (Mod C A)).Localization :=
  Localization.Construction.lift (restriction p ⋙ projection (Mod C A)) (by
    intro M N f hf
    exact Localization.inverts (projection (Mod C A)) (weakEquivalences (Mod C A)) _
      ((restrictionCreatesWeakEquivalences hWA hWB p).le _ hf))

/-- Projection retains the actual scalar restriction on every original module and arrow. -/
theorem rightDerived_projection (p : A ⟶ B) [IsMonHom p] :
    projection (Mod C B) ⋙ rightDerived hWA hWB p = restriction p ⋙ projection (Mod C A) :=
  Localization.Construction.fac _ _

/-- Every represented map is the original restricted map in the original weak localization. -/
theorem rightDerived_map (p : A ⟶ B) [IsMonHom p] {M N : Mod C B} (f : M ⟶ N) :
    (rightDerived hWA hWB p).map ((projection (Mod C B)).map f) =
      (projection (Mod C A)).map ((restriction p).map f) :=
  Functor.congr_hom (rightDerived_projection hWA hWB p) f

/-- The full right comparison is the actual projection identity, without replacing the scalar action. -/
def rightDerivedComparisonIso (p : A ⟶ B) [IsMonHom p] :
    restriction p ⋙ projection (Mod C A) ≅ projection (Mod C B) ⋙ rightDerived hWA hWB p :=
  (eqToIso (rightDerived_projection hWA hWB p)).symm

/-- Each original right comparison component is the identity on the whole restricted module. -/
theorem rightDerivedComparisonIso_app (p : A ⟶ B) [IsMonHom p] (M : Mod C B) :
    (rightDerivedComparisonIso hWA hWB p).hom.app M =
      𝟙 ((projection (Mod C A)).obj ((restriction p).obj M)) := by
  simp only [rightDerivedComparisonIso, Iso.symm_hom, eqToIso.inv, eqToHom_app]
  let X := (projection (Mod C A)).obj ((restriction p).obj M)
  change eqToHom (rfl : X = X) = 𝟙 X
  exact eqToHom_refl X rfl

/-- The direct localized restriction has its full right-derived universal property. -/
theorem rightIsDerived (p : A ⟶ B) [IsMonHom p] :
    (rightDerived hWA hWB p).IsRightDerivedFunctor
      (rightDerivedComparisonIso hWA hWB p).hom (weakEquivalences (Mod C B)) :=
  Functor.isRightDerivedFunctor_of_inverts (weakEquivalences (Mod C B))
    (rightDerived hWA hWB p) (eqToIso (rightDerived_projection hWA hWB p))

/-- Every postcomposition retains the full original right comparison and its universal property. -/
theorem rightPostcomposeIsDerived {H : Type*} [Category* H]
    (p : A ⟶ B) [IsMonHom p] (G : (weakEquivalences (Mod C A)).Localization ⥤ H) :
    (rightDerived hWA hWB p ⋙ G).IsRightDerivedFunctor
      (whiskerRight (rightDerivedComparisonIso hWA hWB p).hom G ≫
        (Functor.associator (projection (Mod C B)) (rightDerived hWA hWB p) G).hom)
      (weakEquivalences (Mod C B)) :=
  Functor.isRightDerivedFunctor_of_inverts (weakEquivalences (Mod C B))
    (rightDerived hWA hWB p ⋙ G)
    ((Functor.associator (projection (Mod C B)) (rightDerived hWA hWB p) G).symm ≪≫
      isoWhiskerRight (eqToIso (rightDerived_projection hWA hWB p)) G)

/-- The actual balanced adjunction and generated source replacement produce all four derived properties. -/
def derivedAdjunctionData (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    QuillenDerivedAdjunctionData (adjunction p) := by
  letI : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
  let L := DerivedFunctorCoherence.left (adjunction p) qA
  let R := rightDerived hWA hWB p
  let α := leftComparison (adjunction p) qA
  let β := (rightDerivedComparisonIso hWA hWB p).hom
  letI : L.IsLeftDerivedFunctor α (weakEquivalences (Mod C A)) := leftIsDerived (adjunction p) qA
  letI : R.IsRightDerivedFunctor β (weakEquivalences (Mod C B)) := rightIsDerived hWA hWB p
  have hLR := DerivedFunctorCoherence.leftPostcomposeIsDerived (adjunction p) qA R
  have hRL := rightPostcomposeIsDerived hWA hWB p L
  letI : (L ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator (projection (Mod C A)) L R).inv ≫ whiskerRight α R)
      (weakEquivalences (Mod C A)) := hLR
  letI : (R ⋙ L).IsRightDerivedFunctor
      (whiskerRight β L ≫ (Functor.associator (projection (Mod C B)) R L).hom)
      (weakEquivalences (Mod C B)) := hRL
  exact
    { leftDerived := L
      rightDerived := R
      leftComparison := α
      rightComparison := β
      leftIsDerived := inferInstance
      rightIsDerived := inferInstance
      leftCompositeIsDerived := hLR
      rightCompositeIsDerived := hRL
      adjunction := (adjunction p).derived (weakEquivalences (Mod C A)) (weakEquivalences (Mod C B)) α β }

/-- The full derived unit retains the actual balanced unit and both original comparison maps. -/
theorem derivedUnit_fac (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) (M : Mod C A) :
    (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.unit.app ((projection (Mod C A)).obj M) ≫
        (derivedAdjunctionData hWA hWB hFA hFB p qA).rightDerived.map
          ((derivedAdjunctionData hWA hWB hFA hFB p qA).leftComparison.app M) =
      (projection (Mod C A)).map ((adjunction p).unit.app M) ≫
        (derivedAdjunctionData hWA hWB hFA hFB p qA).rightComparison.app ((induction p).obj M) := by
  let : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
  let d := derivedAdjunctionData hWA hWB hFA hFB p qA
  let := d.leftIsDerived
  let := d.rightIsDerived
  let := d.leftCompositeIsDerived
  let := d.rightCompositeIsDerived
  exact (adjunction p).derivedη_fac_app (weakEquivalences (Mod C A))
    d.leftComparison d.rightComparison M

/-- The full derived counit retains the original balanced descent and the actual source replacement. -/
theorem derivedCounit_fac (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) (N : Mod C B) :
    (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived.map
        ((derivedAdjunctionData hWA hWB hFA hFB p qA).rightComparison.app N) ≫
      (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.counit.app ((projection (Mod C B)).obj N) =
        (derivedAdjunctionData hWA hWB hFA hFB p qA).leftComparison.app ((restriction p).obj N) ≫
          (projection (Mod C B)).map ((adjunction p).counit.app N) := by
  let : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
  let d := derivedAdjunctionData hWA hWB hFA hFB p qA
  let := d.leftIsDerived
  let := d.rightIsDerived
  let := d.leftCompositeIsDerived
  let := d.rightCompositeIsDerived
  exact (adjunction p).derivedε_fac_app (weakEquivalences (Mod C B))
    d.leftComparison d.rightComparison N

/-- Direct derived restriction agrees naturally with the original chosen-R derived restriction. -/
def rightDerivedChosenIso (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (rB : GeneratedFunctorialReplacements.Data (C := Mod C B)) :
    letI : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
    rightDerived hWA hWB p ≅ DerivedFunctorCoherence.right (adjunction p) rB := by
  letI : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
  letI : (rightDerived hWA hWB p).IsRightDerivedFunctor
      (rightDerivedComparisonIso hWA hWB p).hom (weakEquivalences (Mod C B)) :=
    rightIsDerived hWA hWB p
  letI : (DerivedFunctorCoherence.right (adjunction p) rB).IsRightDerivedFunctor
      (rightComparison (adjunction p) rB) (weakEquivalences (Mod C B)) :=
    DerivedFunctorCoherence.rightIsDerived (adjunction p) rB
  exact Functor.rightDerivedUnique _ _ (rightDerivedComparisonIso hWA hWB p).hom
    (rightComparison (adjunction p) rB) (weakEquivalences (Mod C B))

/-- The whole comparison with chosen-R restriction is the original restricted replacement unit. -/
theorem rightDerivedChosenIso_app (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (rB : GeneratedFunctorialReplacements.Data (C := Mod C B)) (N : Mod C B) :
    letI : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
    (rightDerivedChosenIso hWA hWB hFA hFB p rB).hom.app ((projection (Mod C B)).obj N) =
      (projection (Mod C A)).map ((restriction p).map (rB.r.app N)) := by
  let : (adjunction p).IsQuillenAdjunction := isQuillen hWA hWB hFA hFB p
  let : (rightDerived hWA hWB p).IsRightDerivedFunctor
      (rightDerivedComparisonIso hWA hWB p).hom (weakEquivalences (Mod C B)) :=
    rightIsDerived hWA hWB p
  let : (DerivedFunctorCoherence.right (adjunction p) rB).IsRightDerivedFunctor
      (rightComparison (adjunction p) rB) (weakEquivalences (Mod C B)) :=
    DerivedFunctorCoherence.rightIsDerived (adjunction p) rB
  have h := Functor.rightDerivedNatTrans_app (rightDerived hWA hWB p)
    (DerivedFunctorCoherence.right (adjunction p) rB) (rightDerivedComparisonIso hWA hWB p).hom
    (rightComparison (adjunction p) rB) (weakEquivalences (Mod C B))
    (𝟙 (restriction p ⋙ projection (Mod C A))) N
  change (rightDerivedComparisonIso hWA hWB p).hom.app N ≫
      (rightDerivedChosenIso hWA hWB hFA hFB p rB).hom.app ((projection (Mod C B)).obj N) =
    (𝟙 _) ≫ (rightComparison (adjunction p) rB).app N at h
  rw [rightDerivedComparisonIso_app, DerivedFunctorCoherence.rightComparison_app] at h
  exact (Category.id_comp
    ((rightDerivedChosenIso hWA hWB hFA hFB p rB).hom.app ((projection (Mod C B)).obj N))).symm.trans
      (h.trans (Category.id_comp ((projection (Mod C A)).map ((restriction p).map (rB.r.app N)))))

/-- Equality of the actual scalar maps induces their full localized restriction comparison. -/
def rightDerivedCongrIso {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p'] (h : p = p') :
    rightDerived hWA hWB p ≅ rightDerived hWA hWB p' := by
  cases h
  exact Iso.refl _

/-- Scalar-equality transport is the localization of the original restricted-module transport. -/
theorem rightDerivedCongrIso_hom_app {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    (h : p = p') (N : Mod C B) :
    (rightDerivedCongrIso hWA hWB h).hom.app ((projection (Mod C B)).obj N) =
      (projection (Mod C A)).map ((restrictionCongrIso h).hom.app N) := by
  cases h
  change 𝟙 ((projection (Mod C A)).obj ((restriction p).obj N)) =
    (projection (Mod C A)).map (𝟙 ((restriction p).obj N))
  exact ((projection (Mod C A)).map_id _).symm

/-- The inverse scalar-equality comparison retains the same full original restricted map. -/
theorem rightDerivedCongrIso_inv_app {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    (h : p = p') (N : Mod C B) :
    (rightDerivedCongrIso hWA hWB h).inv.app ((projection (Mod C B)).obj N) =
      (projection (Mod C A)).map ((restrictionCongrIso h).inv.app N) := by
  cases h
  change 𝟙 ((projection (Mod C A)).obj ((restriction p).obj N)) =
    (projection (Mod C A)).map (𝟙 ((restriction p).obj N))
  exact ((projection (Mod C A)).map_id _).symm

/-- The identity derived restriction is the localization of the original identity comparison. -/
def rightDerivedIdIso : rightDerived hWA hWA (𝟙 A) ≅ 𝟭 (weakEquivalences (Mod C A)).Localization := by
  letI : Localization.Lifting (projection (Mod C A)) (weakEquivalences (Mod C A))
      (restriction (𝟙 A) ⋙ projection (Mod C A)) (rightDerived hWA hWA (𝟙 A)) :=
    ⟨eqToIso (rightDerived_projection hWA hWA (𝟙 A))⟩
  letI : Localization.Lifting (projection (Mod C A)) (weakEquivalences (Mod C A))
      (projection (Mod C A)) (𝟭 (weakEquivalences (Mod C A)).Localization) :=
    ⟨Functor.rightUnitor (projection (Mod C A))⟩
  exact Localization.liftNatIso (projection (Mod C A)) (weakEquivalences (Mod C A)) _ _ _ _
    (isoWhiskerRight (restrictionIdIso (A := A)) (projection (Mod C A)) ≪≫
      Functor.leftUnitor (projection (Mod C A)))

/-- The identity derived restriction comparison has the original whole module map at every source. -/
theorem rightDerivedIdIso_hom_app (N : Mod C A) :
    (rightDerivedIdIso hWA).hom.app ((projection (Mod C A)).obj N) =
      (projection (Mod C A)).map ((restrictionIdIso (A := A)).hom.app N) := by
  simp only [rightDerivedIdIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  let X := (projection (Mod C A)).obj ((restriction (𝟙 A)).obj N)
  let Y := (projection (Mod C A)).obj N
  change eqToHom (rfl : X = X) ≫
    ((projection (Mod C A)).map ((restrictionIdIso (A := A)).hom.app N) ≫ 𝟙 Y) ≫ 𝟙 Y = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Category.comp_id _

/-- The inverse identity-derived comparison also retains the full original module map. -/
theorem rightDerivedIdIso_inv_app (N : Mod C A) :
    (rightDerivedIdIso hWA).inv.app ((projection (Mod C A)).obj N) =
      (projection (Mod C A)).map ((restrictionIdIso (A := A)).inv.app N) := by
  simp only [rightDerivedIdIso, Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  let X := (projection (Mod C A)).obj ((restriction (𝟙 A)).obj N)
  let Y := (projection (Mod C A)).obj N
  change (𝟙 Y) ≫
    ((𝟙 Y) ≫ (projection (Mod C A)).map ((restrictionIdIso (A := A)).inv.app N)) ≫
      eqToHom (rfl : X = X) = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

section Composable

variable {D : C} [MonObj D] [ModelCategory (Mod C D)]
  (hWD : weakEquivalences (Mod C D) = (weakEquivalences C).inverseImage (Mod.forget (D := C) D))

/-- Projection keeps both full original restriction stages in the derived composite. -/
theorem rightComposite_projection (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] :
    projection (Mod C D) ⋙ (rightDerived hWB hWD q ⋙ rightDerived hWA hWB p) =
      (restriction q ⋙ restriction p) ⋙ projection (Mod C A) := by
  change (projection (Mod C D) ⋙ rightDerived hWB hWD q) ⋙ rightDerived hWA hWB p = _
  rw [rightDerived_projection]
  change restriction q ⋙ (projection (Mod C B) ⋙ rightDerived hWA hWB p) = _
  rw [rightDerived_projection]
  rfl

/-- The full derived compositor is the localization of the original scalar-restriction compositor. -/
def rightDerivedCompIso (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] :
    rightDerived hWB hWD q ⋙ rightDerived hWA hWB p ≅ rightDerived hWA hWD (p ≫ q) := by
  letI : Localization.Lifting (projection (Mod C D)) (weakEquivalences (Mod C D))
      ((restriction q ⋙ restriction p) ⋙ projection (Mod C A))
      (rightDerived hWB hWD q ⋙ rightDerived hWA hWB p) :=
    ⟨eqToIso (rightComposite_projection hWA hWB hWD p q)⟩
  letI : Localization.Lifting (projection (Mod C D)) (weakEquivalences (Mod C D))
      (restriction (p ≫ q) ⋙ projection (Mod C A)) (rightDerived hWA hWD (p ≫ q)) :=
    ⟨eqToIso (rightDerived_projection hWA hWD (p ≫ q))⟩
  exact Localization.liftNatIso (projection (Mod C D)) (weakEquivalences (Mod C D)) _ _ _ _
    (isoWhiskerRight (restrictionCompIso p q) (projection (Mod C A)))

/-- Every projected derived-composition component retains the complete original restriction map. -/
theorem rightDerivedCompIso_hom_app (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (N : Mod C D) :
    (rightDerivedCompIso hWA hWB hWD p q).hom.app ((projection (Mod C D)).obj N) =
      (projection (Mod C A)).map ((restrictionCompIso p q).hom.app N) := by
  simp only [rightDerivedCompIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  let X := (projection (Mod C A)).obj ((restriction p).obj ((restriction q).obj N))
  let Y := (projection (Mod C A)).obj ((restriction (p ≫ q)).obj N)
  change eqToHom (rfl : X = X) ≫
    (projection (Mod C A)).map ((restrictionCompIso p q).hom.app N) ≫ eqToHom (rfl : Y = Y) = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Every inverse derived-composition component retains the actual inverse restriction map. -/
theorem rightDerivedCompIso_inv_app (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (N : Mod C D) :
    (rightDerivedCompIso hWA hWB hWD p q).inv.app ((projection (Mod C D)).obj N) =
      (projection (Mod C A)).map ((restrictionCompIso p q).inv.app N) := by
  simp only [rightDerivedCompIso, Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  let X := (projection (Mod C A)).obj ((restriction p).obj ((restriction q).obj N))
  let Y := (projection (Mod C A)).obj ((restriction (p ≫ q)).obj N)
  change eqToHom (rfl : Y = Y) ≫
    (projection (Mod C A)).map ((restrictionCompIso p q).inv.app N) ≫ eqToHom (rfl : X = X) = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable
  (hFD : fibrations (Mod C D) = (fibrations C).inverseImage (Mod.forget (D := C) D))

/-- The derived balanced extension compositor is the mate of actual localized restriction composition. -/
def derivedCompositionIso (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B)) :
    (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ⋙
        (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived ≅
      (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).leftDerived :=
  (conjugateIsoEquiv (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
    ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
      (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction)).symm
    (rightDerivedCompIso hWA hWB hWD p q).symm

/-- The full derived extension compositor retains the actual original restriction mate. -/
theorem derivedCompositionIso_conjugate (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B)) :
    conjugateEquiv (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
      ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
        (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction)
      (derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom =
        (rightDerivedCompIso hWA hWB hWD p q).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The actual natural derived units satisfy the complete scalar-composition mate square. -/
theorem derivedComposition_unit_mate (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B))
    (M : (weakEquivalences (Mod C A)).Localization) :
    (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction.unit.app M ≫
        (rightDerivedCompIso hWA hWB hWD p q).inv.app
          ((derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).leftDerived.obj M) =
      ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
        (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction).unit.app M ≫
          (rightDerived hWB hWD q ⋙ rightDerived hWA hWB p).map
            ((derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom.app M) := by
  have h := unit_conjugateEquiv
    (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
    ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
      (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction)
    (derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom M
  rw [derivedCompositionIso_conjugate] at h
  exact h

/-- The complete natural derived counits satisfy the original scalar-composition mate square. -/
theorem derivedComposition_counit_mate (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B))
    (N : (weakEquivalences (Mod C D)).Localization) :
    ((derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ⋙
        (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived).map
      ((rightDerivedCompIso hWA hWB hWD p q).inv.app N) ≫
        ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
          (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction).counit.app N =
      (derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom.app
        ((rightDerived hWA hWD (p ≫ q)).obj N) ≫
          (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction.counit.app N := by
  have h := conjugateEquiv_counit
    (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
    ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
      (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction)
    (derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom N
  rw [derivedCompositionIso_conjugate] at h
  exact h

end Composable

/-- Derived scalar equality transport retains the original comparison on every localized module. -/
def derivedCongrIso {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p'] [HasCoequalizers (Mod C B)]
    (h : p = p') (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ≅
      (derivedAdjunctionData hWA hWB hFA hFB p' qA).leftDerived := by
  cases h
  exact Iso.refl _

/-- The scalar-equality comparison on full derived extensions is the original restriction mate. -/
theorem derivedCongrIso_conjugate {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    [HasCoequalizers (Mod C B)] (h : p = p')
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    conjugateEquiv (derivedAdjunctionData hWA hWB hFA hFB p' qA).adjunction
      (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction
      (derivedCongrIso hWA hWB hFA hFB h qA).hom = (rightDerivedCongrIso hWA hWB h).inv := by
  cases h
  simp [derivedCongrIso, rightDerivedCongrIso]
  rfl

/-- The derived extension along the identity scalar map is naturally the identity functor. -/
def derivedIdentityIso [HasCoequalizers (Mod C A)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).leftDerived ≅
      𝟭 (weakEquivalences (Mod C A)).Localization :=
  (conjugateIsoEquiv (Adjunction.id (C := (weakEquivalences (Mod C A)).Localization))
    (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).adjunction).symm (rightDerivedIdIso hWA).symm

/-- The derived identity extension comparison is the mate of the actual identity restriction comparison. -/
theorem derivedIdentityIso_conjugate [HasCoequalizers (Mod C A)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    conjugateEquiv (Adjunction.id (C := (weakEquivalences (Mod C A)).Localization))
      (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).adjunction
      (derivedIdentityIso hWA hFA qA).hom = (rightDerivedIdIso hWA).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The source scalar identity satisfies the full natural derived-extension unit law. -/
theorem derived_unit_source (p : A ⟶ B) [IsMonHom p]
    [HasCoequalizers (Mod C A)] [HasCoequalizers (Mod C B)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A)) :
    (derivedCompositionIso hWA hWA hFA hFA hWB hFB (𝟙 A) p qA qA).hom ≫
        (derivedCongrIso hWA hWB hFA hFB (Category.id_comp p) qA).hom =
      whiskerRight (derivedIdentityIso hWA hFA qA).hom
        (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ≫
          (Functor.leftUnitor (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived).hom := by
  let a := (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction
  let ai := (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).adjunction
  let ac := (derivedAdjunctionData hWA hWB hFA hFB (𝟙 A ≫ p) qA).adjunction
  apply (conjugateEquiv a (ai.comp a)).injective
  rw [← conjugateEquiv_comp a ac (ai.comp a)]
  rw [← conjugateEquiv_comp a
    ((Adjunction.id (C := (weakEquivalences (Mod C A)).Localization)).comp a) (ai.comp a)]
  rw [derivedCongrIso_conjugate, derivedCompositionIso_conjugate,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight, derivedIdentityIso_conjugate]
  apply Localization.natTrans_ext (projection (Mod C B)) (weakEquivalences (Mod C B))
  intro N
  change (rightDerivedCongrIso hWA hWB (Category.id_comp p)).inv.app ((projection (Mod C B)).obj N) ≫
      (rightDerivedCompIso hWA hWA hWB (𝟙 A) p).inv.app ((projection (Mod C B)).obj N) =
    (𝟙 _) ≫ (rightDerivedIdIso hWA).inv.app ((projection (Mod C A)).obj ((restriction p).obj N))
  rw [rightDerivedCongrIso_inv_app, rightDerivedCompIso_inv_app, rightDerivedIdIso_inv_app]
  change (projection (Mod C A)).map ((restrictionCongrIso (Category.id_comp p)).inv.app N) ≫
      (projection (Mod C A)).map ((restrictionCompIso (𝟙 A) p).inv.app N) =
    (𝟙 _) ≫ (projection (Mod C A)).map ((restrictionIdIso (A := A)).inv.app ((restriction p).obj N))
  have hh : (restrictionCongrIso (Category.id_comp p)).inv.app N ≫
      (restrictionCompIso (𝟙 A) p).inv.app N =
    (restrictionIdIso (A := A)).inv.app ((restriction p).obj N) := by
    apply Mod.hom_ext
    change ((restrictionCongrIso (Category.id_comp p)).inv.app N).hom ≫ 𝟙 N.X = 𝟙 N.X
    simp only [restrictionCongrIso_inv_hom]
    exact Category.id_comp _
  exact ((projection (Mod C A)).map_comp _ _).symm.trans
    ((congrArg (fun f => (projection (Mod C A)).map f) hh).trans (Category.id_comp _).symm)

/-- The target scalar identity satisfies the full natural derived-extension unit law. -/
theorem derived_unit_target (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B)) :
    (derivedCompositionIso hWA hWB hFA hFB hWB hFB p (𝟙 B) qA qB).hom ≫
        (derivedCongrIso hWA hWB hFA hFB (Category.comp_id p) qA).hom =
      whiskerLeft (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived
        (derivedIdentityIso hWB hFB qB).hom ≫
          (Functor.rightUnitor (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived).hom := by
  let a := (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction
  let ai := (derivedAdjunctionData hWB hWB hFB hFB (𝟙 B) qB).adjunction
  let ac := (derivedAdjunctionData hWA hWB hFA hFB (p ≫ 𝟙 B) qA).adjunction
  apply (conjugateEquiv a (a.comp ai)).injective
  rw [← conjugateEquiv_comp a ac (a.comp ai)]
  rw [← conjugateEquiv_comp a
    (a.comp (Adjunction.id (C := (weakEquivalences (Mod C B)).Localization))) (a.comp ai)]
  rw [derivedCongrIso_conjugate, derivedCompositionIso_conjugate,
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft, derivedIdentityIso_conjugate]
  apply Localization.natTrans_ext (projection (Mod C B)) (weakEquivalences (Mod C B))
  intro N
  change (rightDerivedCongrIso hWA hWB (Category.comp_id p)).inv.app ((projection (Mod C B)).obj N) ≫
      (rightDerivedCompIso hWA hWB hWB p (𝟙 B)).inv.app ((projection (Mod C B)).obj N) =
    (𝟙 _) ≫ (rightDerived hWA hWB p).map
      ((rightDerivedIdIso hWB).inv.app ((projection (Mod C B)).obj N))
  rw [rightDerivedCongrIso_inv_app, rightDerivedCompIso_inv_app, rightDerivedIdIso_inv_app]
  change (projection (Mod C A)).map ((restrictionCongrIso (Category.comp_id p)).inv.app N) ≫
      (projection (Mod C A)).map ((restrictionCompIso p (𝟙 B)).inv.app N) =
    (𝟙 _) ≫ (rightDerived hWA hWB p).map
      ((projection (Mod C B)).map ((restrictionIdIso (A := B)).inv.app N))
  have hm := rightDerived_map hWA hWB p ((restrictionIdIso (A := B)).inv.app N)
  rw [hm]
  have hh : (restrictionCongrIso (Category.comp_id p)).inv.app N ≫
      (restrictionCompIso p (𝟙 B)).inv.app N =
    (restriction p).map ((restrictionIdIso (A := B)).inv.app N) := by
    apply Mod.hom_ext
    change ((restrictionCongrIso (Category.comp_id p)).inv.app N).hom ≫ 𝟙 N.X = 𝟙 N.X
    simp only [restrictionCongrIso_inv_hom]
    exact Category.id_comp _
  exact ((projection (Mod C A)).map_comp _ _).symm.trans
    ((congrArg (fun f => (projection (Mod C A)).map f) hh).trans (Category.id_comp _).symm)

section Associativity

variable {D E : C} [MonObj D] [MonObj E]
  [ModelCategory (Mod C D)] [ModelCategory (Mod C E)]
  (hWD : weakEquivalences (Mod C D) = (weakEquivalences C).inverseImage (Mod.forget (D := C) D))
  (hWE : weakEquivalences (Mod C E) = (weakEquivalences C).inverseImage (Mod.forget (D := C) E))
  (hFD : fibrations (Mod C D) = (fibrations C).inverseImage (Mod.forget (D := C) D))
  (hFE : fibrations (Mod C E) = (fibrations C).inverseImage (Mod.forget (D := C) E))

/-- Both full derived scalar-composition routes retain all three chosen replacements and the scalar associator. -/
theorem derived_associativity (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (r : D ⟶ E) [IsMonHom r]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)] [HasCoequalizers (Mod C E)]
    (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
    (qB : GeneratedFunctorialReplacements.Data (C := Mod C B))
    (qD : GeneratedFunctorialReplacements.Data (C := Mod C D)) :
    whiskerRight (derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB).hom
        (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived ≫
      (derivedCompositionIso hWA hWD hFA hFD hWE hFE (p ≫ q) r qA qD).hom ≫
        (derivedCongrIso hWA hWE hFA hFE (Category.assoc p q r) qA).hom =
      (Functor.associator (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived
        (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived
        (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived).hom ≫
        whiskerLeft (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived
          (derivedCompositionIso hWB hWD hFB hFD hWE hFE q r qB qD).hom ≫
            (derivedCompositionIso hWA hWB hFA hFB hWE hFE p (q ≫ r) qA qB).hom := by
  let ap := (derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction
  let aq := (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction
  let ar := (derivedAdjunctionData hWD hWE hFD hFE r qD).adjunction
  let apq := (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
  let aqr := (derivedAdjunctionData hWB hWE hFB hFE (q ≫ r) qB).adjunction
  let al := (derivedAdjunctionData hWA hWE hFA hFE ((p ≫ q) ≫ r) qA).adjunction
  let ad := (derivedAdjunctionData hWA hWE hFA hFE (p ≫ q ≫ r) qA).adjunction
  apply (conjugateEquiv ad ((ap.comp aq).comp ar)).injective
  rw [← conjugateEquiv_comp ad (apq.comp ar) ((ap.comp aq).comp ar)]
  rw [← conjugateEquiv_comp ad al (apq.comp ar)]
  rw [← conjugateEquiv_comp ad (ap.comp (aq.comp ar)) ((ap.comp aq).comp ar)]
  rw [← conjugateEquiv_comp ad (ap.comp aqr) (ap.comp (aq.comp ar))]
  rw [derivedCongrIso_conjugate, derivedCompositionIso_conjugate,
    conjugateEquiv_whiskerRight, derivedCompositionIso_conjugate,
    derivedCompositionIso_conjugate, conjugateEquiv_whiskerLeft, derivedCompositionIso_conjugate,
    conjugateEquiv_associator_hom]
  apply Localization.natTrans_ext (projection (Mod C E)) (weakEquivalences (Mod C E))
  intro N
  change ((rightDerivedCongrIso hWA hWE (Category.assoc p q r)).inv.app
      ((projection (Mod C E)).obj N) ≫
    (rightDerivedCompIso hWA hWD hWE (p ≫ q) r).inv.app ((projection (Mod C E)).obj N)) ≫
      (rightDerivedCompIso hWA hWB hWD p q).inv.app
        ((projection (Mod C D)).obj ((restriction r).obj N)) =
    ((rightDerivedCompIso hWA hWB hWE p (q ≫ r)).inv.app ((projection (Mod C E)).obj N) ≫
      (rightDerived hWA hWB p).map
        ((rightDerivedCompIso hWB hWD hWE q r).inv.app ((projection (Mod C E)).obj N))) ≫ 𝟙 _
  rw [rightDerivedCongrIso_inv_app, rightDerivedCompIso_inv_app, rightDerivedCompIso_inv_app,
    rightDerivedCompIso_inv_app, rightDerivedCompIso_inv_app]
  let f0 := (restrictionCongrIso (Category.assoc p q r)).inv.app N
  let f1 := (restrictionCompIso (p ≫ q) r).inv.app N
  let f2 := (restrictionCompIso p q).inv.app ((restriction r).obj N)
  let g0 := (restrictionCompIso p (q ≫ r)).inv.app N
  let g1 := (restrictionCompIso q r).inv.app N
  let Y := (projection (Mod C A)).obj
    ((restriction p).obj ((restriction q).obj ((restriction r).obj N)))
  change ((projection (Mod C A)).map f0 ≫ (projection (Mod C A)).map f1) ≫
      (projection (Mod C A)).map f2 =
    ((projection (Mod C A)).map g0 ≫
      (rightDerived hWA hWB p).map ((projection (Mod C B)).map g1)) ≫ 𝟙 Y
  have hm := rightDerived_map hWA hWB p g1
  rw [hm]
  have hh : (f0 ≫ f1) ≫ f2 = g0 ≫ (restriction p).map g1 := by
    apply Mod.hom_ext
    change (((restrictionCongrIso (Category.assoc p q r)).inv.app N).hom ≫ 𝟙 N.X) ≫ 𝟙 N.X =
      (𝟙 N.X) ≫ 𝟙 N.X
    simp only [restrictionCongrIso_inv_hom]
    exact congrArg (fun f => f ≫ 𝟙 N.X) (Category.id_comp (𝟙 N.X))
  have hl : ((projection (Mod C A)).map f0 ≫ (projection (Mod C A)).map f1) ≫
      (projection (Mod C A)).map f2 = (projection (Mod C A)).map ((f0 ≫ f1) ≫ f2) :=
    (congrArg (fun f => f ≫ (projection (Mod C A)).map f2)
      ((projection (Mod C A)).map_comp f0 f1).symm).trans
        ((projection (Mod C A)).map_comp (f0 ≫ f1) f2).symm
  exact hl.trans ((congrArg (fun f => (projection (Mod C A)).map f) hh).trans
    (((projection (Mod C A)).map_comp _ _).trans (Category.comp_id _).symm))

section Assembly

variable (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] (r : D ⟶ E) [IsMonHom r]
  [HasCoequalizers (Mod C A)] [HasCoequalizers (Mod C B)]
  [HasCoequalizers (Mod C D)] [HasCoequalizers (Mod C E)]
  (qA : GeneratedFunctorialReplacements.Data (C := Mod C A))
  (qB : GeneratedFunctorialReplacements.Data (C := Mod C B))
  (qD : GeneratedFunctorialReplacements.Data (C := Mod C D))

/-- A coupled scalar-change interface on an actual composable chain.

The stored derived adjunction is identified with the original chosen-source
construction. The stored maps have their original restriction mates, unit
equations and associativity equation. `fullScalarChange` constructs all these
outcomes from the source model data. Repeating a scalar with its identity map
recovers the one-map and two-map instances from the same interface.
-/
structure ScalarChangeDiagram where
  /-- The original balanced adjunction on the first scalar map is Quillen. -/
  quillen : (adjunction p).IsQuillenAdjunction
  /-- The complete derived adjunction on the first scalar map. -/
  derived : QuillenDerivedAdjunctionData (adjunction p)
  /-- The stored data retain the actual original chosen replacement. -/
  derived_original : derived = derivedAdjunctionData hWA hWB hFA hFB p qA
  /-- The whole source-scalar identity comparison. -/
  sourceIdentity : (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).leftDerived ≅
    𝟭 (weakEquivalences (Mod C A)).Localization
  /-- The whole target-scalar identity comparison. -/
  targetIdentity : (derivedAdjunctionData hWB hWB hFB hFB (𝟙 B) qB).leftDerived ≅
    𝟭 (weakEquivalences (Mod C B)).Localization
  /-- The actual first two scalar extensions compose. -/
  firstComposition : (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ⋙
      (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived ≅
    (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).leftDerived
  /-- The actual last two scalar extensions compose. -/
  secondComposition : (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived ⋙
      (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived ≅
    (derivedAdjunctionData hWB hWE hFB hFE (q ≫ r) qB).leftDerived
  /-- Compose after the first two original scalar maps. -/
  leftComposition : (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).leftDerived ⋙
      (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived ≅
    (derivedAdjunctionData hWA hWE hFA hFE ((p ≫ q) ≫ r) qA).leftDerived
  /-- Compose before the last two original scalar maps. -/
  rightComposition : (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ⋙
      (derivedAdjunctionData hWB hWE hFB hFE (q ≫ r) qB).leftDerived ≅
    (derivedAdjunctionData hWA hWE hFA hFE (p ≫ q ≫ r) qA).leftDerived
  /-- Transport the actual equality of the two scalar composites. -/
  scalarAssociator : (derivedAdjunctionData hWA hWE hFA hFE ((p ≫ q) ≫ r) qA).leftDerived ≅
    (derivedAdjunctionData hWA hWE hFA hFE (p ≫ q ≫ r) qA).leftDerived
  /-- The stored source identity is the mate of the original restricted identity. -/
  sourceIdentity_original : conjugateEquiv
      (Adjunction.id (C := (weakEquivalences (Mod C A)).Localization))
      (derivedAdjunctionData hWA hWA hFA hFA (𝟙 A) qA).adjunction sourceIdentity.hom =
    (rightDerivedIdIso hWA).inv
  /-- The stored target identity is the mate of the original restricted identity. -/
  targetIdentity_original : conjugateEquiv
      (Adjunction.id (C := (weakEquivalences (Mod C B)).Localization))
      (derivedAdjunctionData hWB hWB hFB hFB (𝟙 B) qB).adjunction targetIdentity.hom =
    (rightDerivedIdIso hWB).inv
  /-- The first stored compositor has the full original scalar-restriction mate. -/
  firstComposition_original : conjugateEquiv
      (derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction
      ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
        (derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction) firstComposition.hom =
    (rightDerivedCompIso hWA hWB hWD p q).inv
  /-- The second stored compositor has the full original scalar-restriction mate. -/
  secondComposition_original : conjugateEquiv
      (derivedAdjunctionData hWB hWE hFB hFE (q ≫ r) qB).adjunction
      ((derivedAdjunctionData hWB hWD hFB hFD q qB).adjunction.comp
        (derivedAdjunctionData hWD hWE hFD hFE r qD).adjunction) secondComposition.hom =
    (rightDerivedCompIso hWB hWD hWE q r).inv
  /-- Composing after the first scalar pair retains the actual restriction mate. -/
  leftComposition_original : conjugateEquiv
      (derivedAdjunctionData hWA hWE hFA hFE ((p ≫ q) ≫ r) qA).adjunction
      ((derivedAdjunctionData hWA hWD hFA hFD (p ≫ q) qA).adjunction.comp
        (derivedAdjunctionData hWD hWE hFD hFE r qD).adjunction) leftComposition.hom =
    (rightDerivedCompIso hWA hWD hWE (p ≫ q) r).inv
  /-- Composing before the last scalar pair retains the actual restriction mate. -/
  rightComposition_original : conjugateEquiv
      (derivedAdjunctionData hWA hWE hFA hFE (p ≫ q ≫ r) qA).adjunction
      ((derivedAdjunctionData hWA hWB hFA hFB p qA).adjunction.comp
        (derivedAdjunctionData hWB hWE hFB hFE (q ≫ r) qB).adjunction) rightComposition.hom =
    (rightDerivedCompIso hWA hWB hWE p (q ≫ r)).inv
  /-- The stored scalar associator is the mate of its actual equality transport. -/
  scalarAssociator_original : conjugateEquiv
      (derivedAdjunctionData hWA hWE hFA hFE (p ≫ q ≫ r) qA).adjunction
      (derivedAdjunctionData hWA hWE hFA hFE ((p ≫ q) ≫ r) qA).adjunction scalarAssociator.hom =
    (rightDerivedCongrIso hWA hWE (Category.assoc p q r)).inv
  /-- The stored source identity comparison has the complete natural unit law. -/
  sourceUnit : (derivedCompositionIso hWA hWA hFA hFA hWB hFB (𝟙 A) p qA qA).hom ≫
      (derivedCongrIso hWA hWB hFA hFB (Category.id_comp p) qA).hom =
    whiskerRight sourceIdentity.hom (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived ≫
      (Functor.leftUnitor (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived).hom
  /-- The stored target identity comparison has the complete natural unit law. -/
  targetUnit : (derivedCompositionIso hWA hWB hFA hFB hWB hFB p (𝟙 B) qA qB).hom ≫
      (derivedCongrIso hWA hWB hFA hFB (Category.comp_id p) qA).hom =
    whiskerLeft (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived targetIdentity.hom ≫
      (Functor.rightUnitor (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived).hom
  /-- The stored composition maps, with the actual scalar transport, satisfy associativity. -/
  associativity : whiskerRight firstComposition.hom
        (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived ≫
      leftComposition.hom ≫ scalarAssociator.hom =
    (Functor.associator (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived
      (derivedAdjunctionData hWB hWD hFB hFD q qB).leftDerived
      (derivedAdjunctionData hWD hWE hFD hFE r qD).leftDerived).hom ≫
      whiskerLeft (derivedAdjunctionData hWA hWB hFA hFB p qA).leftDerived secondComposition.hom ≫
        rightComposition.hom

/-- Assemble the full original scalar-change statement from its three verified components. -/
def fullScalarChange : ScalarChangeDiagram hWA hWB hFA hFB hWD hWE hFD hFE p q r qA qB qD where
  quillen := isQuillen hWA hWB hFA hFB p
  derived := derivedAdjunctionData hWA hWB hFA hFB p qA
  derived_original := rfl
  sourceIdentity := derivedIdentityIso hWA hFA qA
  targetIdentity := derivedIdentityIso hWB hFB qB
  firstComposition := derivedCompositionIso hWA hWB hFA hFB hWD hFD p q qA qB
  secondComposition := derivedCompositionIso hWB hWD hFB hFD hWE hFE q r qB qD
  leftComposition := derivedCompositionIso hWA hWD hFA hFD hWE hFE (p ≫ q) r qA qD
  rightComposition := derivedCompositionIso hWA hWB hFA hFB hWE hFE p (q ≫ r) qA qB
  scalarAssociator := derivedCongrIso hWA hWE hFA hFE (Category.assoc p q r) qA
  sourceIdentity_original := derivedIdentityIso_conjugate hWA hFA qA
  targetIdentity_original := derivedIdentityIso_conjugate hWB hFB qB
  firstComposition_original := derivedCompositionIso_conjugate hWA hWB hFA hFB hWD hFD p q qA qB
  secondComposition_original := derivedCompositionIso_conjugate hWB hWD hFB hFD hWE hFE q r qB qD
  leftComposition_original := derivedCompositionIso_conjugate hWA hWD hFA hFD hWE hFE (p ≫ q) r qA qD
  rightComposition_original := derivedCompositionIso_conjugate hWA hWB hFA hFB hWE hFE p (q ≫ r) qA qB
  scalarAssociator_original := derivedCongrIso_conjugate hWA hWE hFA hFE (Category.assoc p q r) qA
  sourceUnit := derived_unit_source hWA hWB hFA hFB p qA
  targetUnit := derived_unit_target hWA hWB hFA hFB p qA qB
  associativity := derived_associativity hWA hWB hFA hFB hWD hWE hFD hFE p q r qA qB qD

end Assembly

end Associativity

end Derived

end CreatedModels

section FullTransfers

open CategoryTheory.SmallObject

universe wA wB

variable {IA JA IB JB : MorphismProperty C}
  {sIA : UniformRelativeSourceSmallness.{wA} (IA.strictMap (Mod.free A))}
  {sJA : UniformRelativeSourceSmallness.{wA} (JA.strictMap (Mod.free A))}
  {sIB : UniformRelativeSourceSmallness.{wB} (IB.strictMap (Mod.free B))}
  {sJB : UniformRelativeSourceSmallness.{wB} (JB.strictMap (Mod.free B))}
  (tA : RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C) A) IA JA sIA sJA)
  (tB : RightTransfer.FullModelTransfer (Mod.free B) (Mod.forget (D := C) B) IB JB sIB sJB)

/-- A full original module transfer retains its actual source-rank replacement factory. -/
def replacementsOfTransfer :
    letI : ModelCategory (Mod C A) := tA.model
    GeneratedFunctorialReplacements.Data (C := Mod C A) := by
  letI : ModelCategory (Mod C A) := tA.model
  letI : Fact tA.generationCardinal.cardinal.IsRegular := tA.generationCardinal.regular
  letI : OrderBot tA.generationCardinal.cardinal.ord.ToType := tA.generationCardinal.orderBot
  exact GeneratedFunctorialReplacements.fromGeneration tA.generation

/-- Actual full module transfers supply the created-class inputs of the original scalar Quillen adjunction. -/
theorem isQuillenOfTransfers (p : A ⟶ B) [IsMonHom p] :
    letI : ModelCategory (Mod C A) := tA.model
    letI : ModelCategory (Mod C B) := tB.model
    letI : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
    (adjunction p).IsQuillenAdjunction := by
  let : ModelCategory (Mod C A) := tA.model
  let : ModelCategory (Mod C B) := tB.model
  let : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
  exact isQuillen tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq p

/-- The full original module transfers and their actual generating rank construct the complete derived adjunction. -/
def derivedAdjunctionOfTransfers (p : A ⟶ B) [IsMonHom p] :
    letI : ModelCategory (Mod C A) := tA.model
    letI : ModelCategory (Mod C B) := tB.model
    letI : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
    QuillenDerivedAdjunctionData (adjunction p) := by
  letI : ModelCategory (Mod C A) := tA.model
  letI : ModelCategory (Mod C B) := tB.model
  letI : HasColimitsOfSize.{wA, wA} (Mod C A) := tA.cocomplete
  letI : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
  let qA : GeneratedFunctorialReplacements.Data (C := Mod C A) := by
    letI : Fact tA.generationCardinal.cardinal.IsRegular := tA.generationCardinal.regular
    letI : OrderBot tA.generationCardinal.cardinal.ord.ToType := tA.generationCardinal.orderBot
    exact GeneratedFunctorialReplacements.fromGeneration tA.generation
  exact derivedAdjunctionData tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq p qA

section Chain

universe wD wE

variable {D E : C} [MonObj D] [MonObj E]
  {ID JD IE JE : MorphismProperty C}
  {sID : UniformRelativeSourceSmallness.{wD} (ID.strictMap (Mod.free D))}
  {sJD : UniformRelativeSourceSmallness.{wD} (JD.strictMap (Mod.free D))}
  {sIE : UniformRelativeSourceSmallness.{wE} (IE.strictMap (Mod.free E))}
  {sJE : UniformRelativeSourceSmallness.{wE} (JE.strictMap (Mod.free E))}
  (tD : RightTransfer.FullModelTransfer (Mod.free D) (Mod.forget (D := C) D) ID JD sID sJD)
  (tE : RightTransfer.FullModelTransfer (Mod.free E) (Mod.forget (D := C) E) IE JE sIE sJE)

/-- Full original module transfers assemble the coupled scalar-change interface without outcome inputs. -/
def fullScalarChangeOfTransfers (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (r : D ⟶ E) [IsMonHom r] :
    letI : ModelCategory (Mod C A) := tA.model
    letI : ModelCategory (Mod C B) := tB.model
    letI : ModelCategory (Mod C D) := tD.model
    letI : ModelCategory (Mod C E) := tE.model
    letI : HasColimitsOfSize.{wA, wA} (Mod C A) := tA.cocomplete
    letI : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
    letI : HasColimitsOfSize.{wD, wD} (Mod C D) := tD.cocomplete
    letI : HasColimitsOfSize.{wE, wE} (Mod C E) := tE.cocomplete
    ScalarChangeDiagram tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq
      tD.weak_eq tE.weak_eq tD.fibrations_eq tE.fibrations_eq p q r
      (replacementsOfTransfer tA) (replacementsOfTransfer tB) (replacementsOfTransfer tD) := by
  letI : ModelCategory (Mod C A) := tA.model
  letI : ModelCategory (Mod C B) := tB.model
  letI : ModelCategory (Mod C D) := tD.model
  letI : ModelCategory (Mod C E) := tE.model
  letI : HasColimitsOfSize.{wA, wA} (Mod C A) := tA.cocomplete
  letI : HasColimitsOfSize.{wB, wB} (Mod C B) := tB.cocomplete
  letI : HasColimitsOfSize.{wD, wD} (Mod C D) := tD.cocomplete
  letI : HasColimitsOfSize.{wE, wE} (Mod C E) := tE.cocomplete
  exact fullScalarChange tA.weak_eq tB.weak_eq tA.fibrations_eq tB.fibrations_eq
    tD.weak_eq tE.weak_eq tD.fibrations_eq tE.fibrations_eq p q r
      (replacementsOfTransfer tA) (replacementsOfTransfer tB) (replacementsOfTransfer tD)

end Chain

end FullTransfers

end HomotopicalAlgebra.ModuleTransfer.ScalarChange
