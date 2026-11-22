/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientBase

/-!
# Complete original coefficient data and module-map transport

Equality of the entire coefficient commutative monoid transports module objects,
free constructors and arbitrary module maps. The original coefficient pre-map
retains both original endpoint transports under every functor image.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.ModuleCoefficientData

universe uD vD
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]

/-- Equality of the complete coefficient monoid transports the full module carrier. -/
def equivalence {B B' : CommMon D} (h : B = B') : Mod D B.X ≌ Mod D B'.X := by
  cases h
  exact CategoryTheory.Equivalence.refl

/-- The transport retains the entire original underlying object. -/
theorem equivalence_obj_X {B B' : CommMon D} (h : B = B') (N : Mod D B.X) :
    ((equivalence h).functor.obj N).X = N.X := by
  cases h
  rfl

/-- Its inverse retains that same entire underlying object. -/
theorem equivalence_inverse_obj_X {B B' : CommMon D} (h : B = B') (N : Mod D B'.X) :
    ((equivalence h).inverse.obj N).X = N.X := by
  cases h
  rfl

/-- Every complete underlying module map is retained by the monoid-data transport. -/
theorem equivalence_map_hom {B B' : CommMon D} (h : B = B')
    {N N' : Mod D B.X} (f : N ⟶ N') :
    ((equivalence h).functor.map f).hom =
      (eqToIso (equivalence_obj_X h N)).hom ≫ f.hom ≫
        (eqToIso (equivalence_obj_X h N')).inv := by
  cases h
  change f.hom = 𝟙 N.X ≫ f.hom ≫ 𝟙 N'.X
  simp only [Category.id_comp, Category.comp_id]

/-- The inverse transport retains each given entire module map. -/
theorem equivalence_inverse_map_hom {B B' : CommMon D} (h : B = B')
    {N N' : Mod D B'.X} (f : N ⟶ N') :
    ((equivalence h).inverse.map f).hom =
      (eqToIso (equivalence_inverse_obj_X h N)).hom ≫ f.hom ≫
        (eqToIso (equivalence_inverse_obj_X h N')).inv := by
  cases h
  change f.hom = 𝟙 N.X ≫ f.hom ≫ 𝟙 N'.X
  simp only [Category.id_comp, Category.comp_id]

/-- The original free constructor retains all fields under the same full monoid equality. -/
theorem equivalence_free_obj {B B' : CommMon D} (h : B = B') (P : D) :
    (equivalence h).functor.obj ((Mod.free B.X).obj P) = (Mod.free B'.X).obj P := by
  cases h
  rfl

/-- The complete free functor and all its maps are transported by that same data equality. -/
def freeFunctorIso {B B' : CommMon D} (h : B = B') :
    Mod.free B.X ⋙ (equivalence h).functor ≅ Mod.free B'.X := by
  cases h
  exact Functor.rightUnitor (Mod.free B.X)

/-- Every original ambient source map retains the full free-map naturality square. -/
theorem freeFunctorIso_naturality {B B' : CommMon D} (h : B = B')
    {P Q : D} (f : P ⟶ Q) :
    (equivalence h).functor.map ((Mod.free B.X).map f) ≫
      (freeFunctorIso h).hom.app Q =
    (freeFunctorIso h).hom.app P ≫ (Mod.free B'.X).map f :=
  (freeFunctorIso h).hom.naturality f

end NativeOmegaRecovery.ModuleCoefficientData

namespace NativeOmegaRecovery.NativeScalarCoefficient

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided
  PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction

/-- The actual coefficient module category is the original carrier
under its full given sphere data. -/
def coefficientModuleEquivalence : Mod Sequence.{u, v} A.{u, v}.X ≌ OriginalModule.{u, v} :=
  ModuleCoefficientData.equivalence
    (B := A.{u, v})
    (B' := CommMon.mk
      (mon := PointedCGWH.sphereSequenceMonObj.{u, v})
      (comm := PointedCGWH.sphereSequenceIsCommMonObj.{u, v})
      (PointedCGWH.sphereSequence.{u, v})) rfl

/-- The actual forward carrier transport retains every original coefficient module map. -/
theorem coefficientModuleEquivalence_map_hom
    {N N' : Mod Sequence.{u, v} A.{u, v}.X} (f : N ⟶ N') :
    (coefficientModuleEquivalence.{u, v}.functor.map f).hom = f.hom := rfl

/-- The whole actual original pre-map keeps its literal component
after this full carrier transport. -/
theorem coefficientPreArrow_transport_level (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) (n : I) :
    (coefficientModuleEquivalence.{u, v}.functor.map
        (coefficientPreArrow r f N).hom).hom.natTrans.app n =
      (coefficientPreArrow r f N).hom.hom.natTrans.app n := by
  have h := coefficientModuleEquivalence_map_hom (coefficientPreArrow r f N).hom
  exact congrArg (fun g => g.natTrans.app n) h


/-- The inverse data transport retains the full original module map
before taking components. -/
theorem coefficientModuleEquivalence_inverse_map_hom
    {N N' : OriginalModule.{u, v}} (f : N ⟶ N') :
    (coefficientModuleEquivalence.{u, v}.inverse.map f).hom = f.hom := rfl

/-- Evaluation on the actual coefficient module category retains its exact original instance. -/
abbrev coefficientLevelFunctor (n : I) :
    Mod Sequence.{u, v} A.{u, v}.X ⥤ V.{u, v} :=
  Mod.dayEvaluation A.{u, v}.X n

/-- The full original module carrier is evaluated through its given complete sphere data. -/
def originalLevelFunctor (n : I) : OriginalModule.{u, v} ⥤ V.{u, v} :=
  coefficientModuleEquivalence.{u, v}.inverse ⋙ coefficientLevelFunctor n

/-- Each original map has its literal component under the same data-aware evaluation. -/
theorem originalLevelFunctor_map (n : I) {N N' : OriginalModule.{u, v}} (f : N ⟶ N') :
    (originalLevelFunctor n).map f = f.hom.natTrans.app n := by
  have h := coefficientModuleEquivalence_inverse_map_hom f
  exact congrArg (fun g => g.natTrans.app n) h

/-- The whole transported map keeps all three original module arrows before evaluation. -/
theorem originalCoefficientModuleMap_eq (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    originalCoefficientModuleMap r f N =
      (originalToPreLeftIso r f N).hom ≫ (coefficientPreArrow r f N).hom ≫
        (originalToPreRightIso r f N).inv := rfl

/-- The literal original component equation, with all given source maps and endpoint transports. -/
def originalCoefficientComponentEquation (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) (n : I) : Prop :=
    (originalCoefficientModuleMap r f N).hom.natTrans.app n =
      (originalToPreLeftIso r f N).hom.hom.natTrans.app n ≫
        (coefficientPreArrow r f N).hom.hom.natTrans.app n ≫
          (originalToPreRightIso r f N).inv.hom.natTrans.app n


universe uE vE

/-- Every genuine functor preserves the whole given original coefficient map
and both endpoint transports. -/
theorem originalCoefficientModuleMap_image {E : Type uE} [Category.{vE} E]
    (L : OriginalModule.{u, v} ⥤ E) (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    L.map (originalCoefficientModuleMap r f N) =
      L.map (originalToPreLeftIso r f N).hom ≫
        L.map (coefficientPreArrow r f N).hom ≫
          L.map (originalToPreRightIso r f N).inv := by
  let G : OriginalModule.{u, v} := (coefficientPreArrow r f N).left
  let G' : OriginalModule.{u, v} := (coefficientPreArrow r f N).right
  let a : originalHom r M N ⟶ G := (originalToPreLeftIso r f N).hom
  let p : G ⟶ G' := (coefficientPreArrow r f N).hom
  let b : G' ⟶ originalHom r M' N := (originalToPreRightIso r f N).inv
  have h₀ := congrArg
    (fun k : originalHom r M N ⟶ originalHom r M' N => L.map k)
    (originalCoefficientModuleMap_eq r f N)
  exact h₀.trans ((L.map_comp a (p ≫ b)).trans
    (congrArg (fun z => L.map a ≫ z) (L.map_comp p b)))

/-- Equality of four complete maps retains the entire three-arrow equation. -/
theorem coefficientFourMaps {E : Type uE} [Category.{vE} E] {X Y Z T : E}
    {m m' : X ⟶ T} {a a' : X ⟶ Y} {p p' : Y ⟶ Z} {b b' : Z ⟶ T}
    (h : m = a ≫ p ≫ b) (hm : m = m') (ha : a = a') (hp : p = p') (hb : b = b') :
    m' = a' ≫ p' ≫ b' := by
  rw [← hm, ← ha, ← hp, ← hb]
  exact h

/-- Every three-arrow original module composite keeps its entire underlying sequence map. -/
theorem originalThreeArrow_hom {N₀ N₁ N₂ N₃ : OriginalModule.{u, v}}
    (a : N₀ ⟶ N₁) (p : N₁ ⟶ N₂) (b : N₂ ⟶ N₃) :
    (a ≫ p ≫ b).hom = a.hom ≫ p.hom ≫ b.hom := rfl

/-- The entire native coefficient map has the same original underlying three-arrow sequence map. -/
theorem originalCoefficientModuleMap_hom (r : I) {M' M : V.{u, v}} (f : M' ⟶ M)
    (N : OriginalModule.{u, v}) :
    (originalCoefficientModuleMap r f N).hom =
      (originalToPreLeftIso r f N).hom.hom ≫
        (coefficientPreArrow r f N).hom.hom ≫ (originalToPreRightIso r f N).inv.hom := by
  have hm := congrArg
    (fun k : originalHom r M N ⟶ originalHom r M' N => k.hom)
    (originalCoefficientModuleMap_eq r f N)
  exact hm.trans (originalThreeArrow_hom (originalToPreLeftIso r f N).hom
    (coefficientPreArrow r f N).hom (originalToPreRightIso r f N).inv)

/-- Three ordinary sequence maps retain every component of their given composition. -/
theorem sequenceThreeArrow_level {Q₀ Q₁ Q₂ Q₃ : Sequence.{u, v}}
    (a : Q₀ ⟶ Q₁) (p : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃) (n : I) :
    (a ≫ p ≫ b).natTrans.app n =
      a.natTrans.app n ≫ p.natTrans.app n ≫ b.natTrans.app n := rfl

end NativeOmegaRecovery.NativeScalarCoefficient

namespace NativeOmegaRecovery.FreeFunctionCarrierComparison

universe uD vD uT vT
variable {D : Type uD} [Category.{vD} D] {T : Type uT} [Category.{vT} T]
  (E : D ≌ T) {F F' : D ⥤ D} {R R' : T ⥤ T}

/-- The actual complete target map may be identified before collapsing the original carrier
counit. -/
theorem collapse_coefficient_with_target (p : F ⟶ F') (q : R ⟶ R')
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (e' : F' ≅ E.functor ⋙ R' ⋙ E.inverse)
    (g : E.functor ⋙ R ⋙ E.inverse ⟶ E.functor ⋙ R' ⋙ E.inverse)
    (hg : g = Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse))
    (h : p ≫ e'.hom = e.hom ≫ g) :
    Functor.whiskerRight p E.functor ≫ (collapse E e').hom =
      (collapse E e).hom ≫ Functor.whiskerLeft E.functor q := by
  apply collapse_coefficient E p q e e'
  exact h.trans (congrArg (fun z => e.hom ≫ z) hg)


/-- A genuine carrier functor retains a given whole module coefficient square before any target
identification. -/
theorem whiskerRight_coefficient {D : Type uD} [Category.{vD} D]
    {T : Type uT} [Category.{vT} T] (L : D ⥤ T)
    {F F' K K' : D ⥤ D} (p : F ⟶ F') (e : F ≅ K) (e' : F' ≅ K')
    (g : K ⟶ K') (h : p ≫ e'.hom = e.hom ≫ g) :
    Functor.whiskerRight p L ≫ (Functor.isoWhiskerRight e' L).hom =
      (Functor.isoWhiskerRight e L).hom ≫ Functor.whiskerRight g L := by
  apply NatTrans.ext
  funext N
  have hn := congrArg (fun z => L.map (z.app N)) h
  simp only [NatTrans.comp_app, Functor.map_comp] at hn
  exact hn

/-- The entire original carrier counit is natural in every genuine target functor map. -/
theorem targetRecovery_coefficient (q : R ⟶ R') :
    Functor.whiskerRight
        (Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse)) E.functor ≫
      (Functor.isoWhiskerLeft (E.functor ⋙ R') E.counitIso).hom =
    (Functor.isoWhiskerLeft (E.functor ⋙ R) E.counitIso).hom ≫
      Functor.whiskerLeft E.functor q := by
  apply NatTrans.ext
  funext N
  let b := q.app (E.functor.obj N)
  have h := E.counitIso.hom.naturality b
  exact h

/-- Identification of the actual target map precedes the naturality of the entire original
carrier counit. -/
theorem targetRecovery_coefficient_with_map (q : R ⟶ R')
    (g : E.functor ⋙ R ⋙ E.inverse ⟶ E.functor ⋙ R' ⋙ E.inverse)
    (hg : g = Functor.whiskerLeft E.functor (Functor.whiskerRight q E.inverse)) :
    Functor.whiskerRight g E.functor ≫
      (Functor.isoWhiskerLeft (E.functor ⋙ R') E.counitIso).hom =
    (Functor.isoWhiskerLeft (E.functor ⋙ R) E.counitIso).hom ≫
      Functor.whiskerLeft E.functor q := by
  rw [hg]
  exact targetRecovery_coefficient E q

end NativeOmegaRecovery.FreeFunctionCarrierComparison

namespace NativeOmegaRecovery.ModuleCoefficientData

universe uD vD uT vT
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]

/-- Equality of the full coefficient transports a given entire carrier equivalence. -/
def carrierEquivalence {B B' : CommMon D} (h : B = B')
    {T : Type uT} [Category.{vT} T] (E : Mod D B'.X ≌ T) : Mod D B.X ≌ T := by
  cases h
  exact E

section Closed
variable [MonoidalClosed D] [Limits.HasEqualizers D]

/-- The entire original internal-Hom module, including its action, is retained by monoid
transport. -/
theorem equivalence_internalHom_obj {B B' : CommMon D} (h : B = B')
    (P N : Mod D B.X) :
    (equivalence h).functor.obj ((Mod.internalHom B P).obj N) =
      (Mod.internalHom B' ((equivalence h).functor.obj P)).obj
        ((equivalence h).functor.obj N) := by
  cases h
  rfl

/-- Both original internal-Hom functors and all target maps retain the full monoid-data
transport. -/
def internalHomFunctorIso {B B' : CommMon D} (h : B = B') (P : Mod D B.X) :
    Mod.internalHom B P ⋙ (equivalence h).functor ≅
      (equivalence h).functor ⋙ Mod.internalHom B' ((equivalence h).functor.obj P) := by
  cases h
  exact Functor.rightUnitor (Mod.internalHom B P) ≪≫
    (Functor.leftUnitor (Mod.internalHom B P)).symm

/-- Every entire target-module map satisfies the same transported internal-Hom naturality. -/
theorem internalHomFunctorIso_naturality {B B' : CommMon D} (h : B = B')
    (P : Mod D B.X) {N N' : Mod D B.X} (f : N ⟶ N') :
    (equivalence h).functor.map ((Mod.internalHom B P).map f) ≫
        (internalHomFunctorIso h P).hom.app N' =
      (internalHomFunctorIso h P).hom.app N ≫
        (Mod.internalHom B' ((equivalence h).functor.obj P)).map
          ((equivalence h).functor.map f) :=
  (internalHomFunctorIso h P).hom.naturality f

end Closed
end NativeOmegaRecovery.ModuleCoefficientData

namespace NativeOmegaRecovery.NativeScalarCoefficient

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided
  PointedCGWH.originalSymmetricSequenceSymmetric

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction
open PointedCGWH.Spectra.NativeStableMonoidal

/-- The full original operator equivalence is transported through the actual given sphere monoid
data. -/
def coefficientOperatorEquivalence : Mod Sequence.{u, v} A.{u, v}.X ≌ NativeCarrier.{u, v} :=
  ModuleCoefficientData.carrierEquivalence
    (B := A.{u, v})
    (B' := CommMon.mk (mon := PointedCGWH.sphereSequenceMonObj.{u, v})
      (comm := PointedCGWH.sphereSequenceIsCommMonObj.{u, v}) PointedCGWH.sphereSequence.{u, v})
    rfl moduleOperatorEquivalence.{u, v}

/-- Every functor, inverse, unit, counit and triangle is the full original equivalence record. -/
theorem coefficientOperatorEquivalence_eq_original :
    coefficientOperatorEquivalence.{u, v} = moduleOperatorEquivalence.{u, v} := rfl

/-- The original target map retains the full carrier and inverse supplied by the same original
record. -/
theorem targetModuleSourceNat_coefficient_whisker (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    targetModuleSourceNat r f =
      Functor.whiskerLeft coefficientOperatorEquivalence.{u, v}.functor
        (Functor.whiskerRight
          (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
            (cotensorSourceNat f)) coefficientOperatorEquivalence.{u, v}.inverse) := rfl

/-- The original entire module/operator comparison retains that same original counit collapse. -/
theorem moduleOperatorComparison_coefficient_collapse (r : I) (M : V.{u, v}) :
    moduleOperatorComparison.{u, v} r M =
      FreeFunctionCarrierComparison.collapse coefficientOperatorEquivalence.{u, v}
        (moduleComparisonNat.{u, v} r M) := rfl

/-- The native full coefficient module square is retained by the entire original carrier functor. -/
theorem moduleComparisonNat_coefficient_carrier (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    Functor.whiskerRight
        (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r f))
        coefficientOperatorEquivalence.{u, v}.functor ≫
      (Functor.isoWhiskerRight (moduleComparisonNat r M')
        coefficientOperatorEquivalence.{u, v}.functor).hom =
    (Functor.isoWhiskerRight (moduleComparisonNat r M)
        coefficientOperatorEquivalence.{u, v}.functor).hom ≫
      Functor.whiskerRight (targetModuleSourceNat r f)
        coefficientOperatorEquivalence.{u, v}.functor :=
  FreeFunctionCarrierComparison.whiskerRight_coefficient
    coefficientOperatorEquivalence.{u, v}.functor
    (FreeModuleSource.pre A.{u, v} (DayFreeCoefficient.freeSequenceMap r f))
    (moduleComparisonNat r M) (moduleComparisonNat r M') (targetModuleSourceNat r f)
    (moduleComparisonNat_coefficient r f)

/-- The given entire original carrier counit recovers the actual target operator functor. -/
def coefficientTargetRecoveryIso (r : I) (M : V.{u, v}) :=
  Functor.isoWhiskerLeft
    (moduleToOperator.{u, v} ⋙ PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor M)
    operatorRecoveryNatIso.{u, v}

/-- The original full comparison retains both its entire module map and original carrier
recovery. -/
theorem moduleOperatorComparison_coefficient_factors (r : I) (M : V.{u, v}) :
    moduleOperatorComparison r M =
      Functor.isoWhiskerRight (moduleComparisonNat r M)
        coefficientOperatorEquivalence.{u, v}.functor ≪≫ coefficientTargetRecoveryIso r M := rfl

/-- The full original forward comparison has those same two entire transformation factors. -/
theorem moduleOperatorComparison_coefficient_hom_factors (r : I) (M : V.{u, v}) :
    (moduleOperatorComparison r M).hom =
      (Functor.isoWhiskerRight (moduleComparisonNat r M)
        coefficientOperatorEquivalence.{u, v}.functor).hom ≫
          (coefficientTargetRecoveryIso r M).hom := by
  have h := congrArg (fun e => e.hom) (moduleOperatorComparison_coefficient_factors r M)
  exact h.trans (Iso.trans_hom _ _)

/-- The full original target pre-map has its given original carrier and inverse-carrier
whiskering. -/
theorem targetModuleSourceNat_original_whisker (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    targetModuleSourceNat r f =
      Functor.whiskerLeft moduleToOperator.{u, v}
        (Functor.whiskerRight
          (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
            (cotensorSourceNat f)) operatorToModule.{u, v}) := rfl

/-- The actual target pre-map preserves the entire original operator recovery square. -/
theorem targetModuleSourceNat_recovery_square (r : I) {M' M : V.{u, v}} (f : M' ⟶ M) :
    Functor.whiskerRight (targetModuleSourceNat r f) moduleToOperator.{u, v} ≫
      (coefficientTargetRecoveryIso r M').hom =
    (coefficientTargetRecoveryIso r M).hom ≫
      Functor.whiskerLeft moduleToOperator.{u, v}
        (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
          (cotensorSourceNat f)) := by
  apply NatTrans.ext
  funext N
  let b := (Functor.whiskerLeft (PointedCGWH.SymmetricShift.functor.{u, v} r)
    (cotensorSourceNat f)).app (moduleToOperator.{u, v}.obj N)
  have h := operatorRecoveryNatIso.{u, v}.hom.naturality b
  exact h

end NativeOmegaRecovery.NativeScalarCoefficient
