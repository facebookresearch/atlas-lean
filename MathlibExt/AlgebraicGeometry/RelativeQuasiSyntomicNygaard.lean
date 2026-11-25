/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasiSyntomicPrismSites
public import MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology
public import MathlibExt.AlgebraicGeometry.PrismaticDecalageModels
public import MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Relative quasisyntomic Nygaard sheaves over arbitrary bounded prisms

The large basis consists of actual quasisyntomic algebras under the specified
residue algebra, with largeness over the original A/I. Initial relative prism
lifts supply the actual structural rings and their universal maps. Frobenius
twist uses completed derived scalar extension along phi_A. Nygaard is the
actual inverse image of I^i under its H0 Frobenius, followed by sheafification
and genuine derived global sections. It is not the absolute ideal preimage
under an untwisted perfect-base Frobenius.

No perfectness of the base prism is imposed. Constructing the initial lifts,
their base-module completeness and the normalized Frobenius diagram is one
joint source request; it contains no qsyn/prismatic descent isomorphism.

References: Bhatt–Scholze, arXiv:1905.08229v4, Definitions 15.1 and
Theorems 15.2–15.3; BMS19 arXiv:1802.03261v2, Section 4.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeQuasiSyntomicNygaard

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open LargeQuasiSyntomicAlgebras PrismaticNygaardModels

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (R : CommAlgCat.{0} P.Residue)

/-- The actual relative qsyn objects under R, with their original A/I scalar action. -/
structure Algebra where
  ring : CommAlgCat.{0} P.Residue
  under : R →ₐ[P.Residue] ring
  [tensor : HasTensor ring]
  quasisyntomic : letI := under.toRingHom.toAlgebra
    QuasiSyntomic p R ring

attribute [instance] Algebra.tensor

namespace Algebra

@[ext] structure Hom (U V : Algebra p P R) where
  map : U.ring →ₐ[P.Residue] V.ring
  under : map.comp U.under = V.under

instance : Category (Algebra p P R) where
  Hom := Hom p P R
  id U := ⟨AlgHom.id _ _, by ext x; rfl⟩
  comp f g := ⟨g.map.comp f.map, by rw [AlgHom.comp_assoc, f.under, g.under]⟩
  id_comp _ := by apply Hom.ext; ext x; rfl
  comp_id _ := by apply Hom.ext; ext x; rfl
  assoc _ _ _ := by apply Hom.ext; ext x; rfl

end Algebra

def IsCover {U V : Algebra p P R} (f : U ⟶ V) : Prop :=
  (letI := f.map.toRingHom.toAlgebra; Nonempty (QuasiSyntomic p U.ring V.ring)) ∧
  ∀ m : ℕ, letI := (QuasiSyntomicPrismSites.scalarQuotient p
    f.map.toRingHom (m + 1)).toAlgebra
    Module.FaithfullyFlat
      (U.ring ⧸ Ideal.span {(p : U.ring) ^ (m + 1)})
      (V.ring ⧸ Ideal.span {(p : V.ring) ^ (m + 1)})

/-- The true large A/I-algebra basis, without a perfectoid-base restriction. -/
abbrev Basis :=
  (show ObjectProperty (Algebra p P R) from fun B ↦
    Nonempty (LargeQuasiSyntomic p P.Residue B.ring)).FullSubcategory

def topology : GrothendieckTopology (Basis p P R)ᵒᵖ :=
  sInf {J | ∀ (U V : Basis p P R) (f : U ⟶ V),
    IsCover p P R f.hom →
      Sieve.ofArrows (fun _ : Unit ↦ op V) (fun _ ↦ f.op) ∈ J (op U)}

variable {R}

/-- Reindex a relative lift by the actual A/I algebra map. -/
def changeResidue {S T : CommAlgCat.{0} P.Residue}
    (f : S →ₐ[P.Residue] T) (V : Lift p P T) : Lift p P S where
  prism := V.prism
  base := V.base
  residue := V.residue.comp f.toRingHom
  scalar := by
    apply RingHom.ext
    intro a
    change V.residue (f (algebraMap P.Residue S a)) = (BoundedPrisms.Hom.residue p V.base) a
    rw [f.commutes]
    exact congrArg (fun f : P.Residue →+* V.prism.Residue ↦ f a) V.scalar

def initialMap {S T : CommAlgCat.{0} P.Residue}
    (U : InitialLift p P S) (V : InitialLift p P T) (f : S →ₐ[P.Residue] T) :
    U.lift.prism ⟶ V.lift.prism :=
  (U.initial.to (changeResidue p P f V.lift)).map

theorem initialMap_base {S T : CommAlgCat.{0} P.Residue}
    (U : InitialLift p P S) (V : InitialLift p P T) (f : S →ₐ[P.Residue] T) :
    U.lift.base ≫ initialMap p P U V f = V.lift.base :=
  (U.initial.to (changeResidue p P f V.lift)).base

private theorem residue_comp {Q Q' Q'' : Prism.{0} p} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    (BoundedPrisms.Hom.residue p (f ≫ g)) =
      (BoundedPrisms.Hom.residue p g).comp (BoundedPrisms.Hom.residue p f) := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem initialMap_id {S : CommAlgCat.{0} P.Residue} (U : InitialLift p P S) :
    initialMap p P U U (AlgHom.id P.Residue S) = 𝟙 U.lift.prism := by
  change (U.initial.to U.lift).map = (𝟙 U.lift : U.lift ⟶ U.lift).map
  exact congrArg LiftHom.map (U.initial.hom_ext _ _)

theorem initialMap_comp {S T V : CommAlgCat.{0} P.Residue}
    (U : InitialLift p P S) (W : InitialLift p P T) (Z : InitialLift p P V)
    (f : S →ₐ[P.Residue] T) (g : T →ₐ[P.Residue] V) :
    initialMap p P U Z (g.comp f) =
      initialMap p P U W f ≫ initialMap p P W Z g := by
  let h : U.lift ⟶ changeResidue p P (g.comp f) Z.lift :=
    ⟨initialMap p P U W f ≫ initialMap p P W Z g,
      by
        change U.lift.base ≫ (initialMap p P U W f ≫ initialMap p P W Z g) = Z.lift.base
        rw [← Category.assoc, initialMap_base, initialMap_base], by
        change (BoundedPrisms.Hom.residue p
          (initialMap p P U W f ≫ initialMap p P W Z g)).comp U.lift.residue =
            Z.lift.residue.comp (g.comp f).toRingHom
        rw [residue_comp, RingHom.comp_assoc]
        have hf : (BoundedPrisms.Hom.residue p (initialMap p P U W f)).comp U.lift.residue =
            W.lift.residue.comp f.toRingHom :=
          (U.initial.to (changeResidue p P f W.lift)).residue
        have hg : (BoundedPrisms.Hom.residue p (initialMap p P W Z g)).comp W.lift.residue =
            Z.lift.residue.comp g.toRingHom :=
          (W.initial.to (changeResidue p P g Z.lift)).residue
        rw [hf, ← RingHom.comp_assoc, hg]
        rfl⟩
  exact congrArg LiftHom.map (U.initial.hom_ext _ h)

variable (R) (D : ∀ B : Basis p P R, InitialLift p P B.obj.ring)

abbrev map {U V : Basis p P R} (f : U ⟶ V) :=
  initialMap p P (D U) (D V) f.hom.map

/-- Actual structural rings and their universal relative-prism maps. -/
def deltaAlgebras : ((Basis p P R)ᵒᵖ)ᵒᵖ ⥤ CommAlgCat.{1} P.ring where
  obj B := CommAlgCat.of P.ring (ULift.{1} (D B.unop.unop).lift.prism.ring)
  map f := CommAlgCat.ofHom
    { toFun x := ULift.up ((map p P R D f.unop.unop).hom x.down)
      map_zero' := ULift.ext (map_zero _)
      map_one' := ULift.ext (map_one _)
      map_add' x y := ULift.ext (map_add _ x.down y.down)
      map_mul' x y := ULift.ext (map_mul _ x.down y.down)
      commutes' a := by
        apply ULift.ext
        exact congrArg (fun f : P ⟶ (D _).lift.prism ↦ f.hom a)
          (initialMap_base p P (D _) (D _) f.unop.unop.hom.map) }
  map_id _ := by
    apply CommAlgCat.hom_ext
    ext x
    exact congrArg (fun f ↦ f.hom x.down) (initialMap_id p P (D _))
  map_comp f g := by
    apply CommAlgCat.hom_ext
    ext x
    exact congrArg (fun f ↦ f.hom x.down)
      (initialMap_comp p P (D _) (D _) (D _) f.unop.unop.hom.map g.unop.unop.hom.map)

abbrev deltaPresheaf := deltaAlgebras p P R D ⋙
  PrismaticCosimplicialAlgebras.algebraModules P.ring

abbrev deltaDerived := deltaPresheaf p P R D ⋙
  DerivedCategory.singleFunctor (Modules P.ring) 0

variable [HasExtension (DeltaRing.frobenius p P.ring)]
  (C : Completion P.ring (completionIdeal p P.ideal))

abbrev twistedDerived := deltaDerived p P R D ⋙
  completedExtension (DeltaRing.frobenius p P.ring) C

abbrev twistedModules := twistedDerived p P R D C ⋙
  DerivedCategory.homologyFunctor (Modules P.ring) 0

/-- The actual relative Frobenius is fixed at every large basis object. -/
structure FrobeniusDiagram
    (h : ∀ B : Basis p P R, IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P B.obj.ring (D B).lift)) where
  map : twistedDerived p P R D C ⟶ deltaDerived p P R D
  prescribed : ∀ B : ((Basis p P R)ᵒᵖ)ᵒᵖ, map.app B =
    completedFrobenius p P B.unop.unop.obj.ring (D B.unop.unop).lift C (h B.unop.unop)

variable {C} {h : ∀ B : Basis p P R, IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P B.obj.ring (D B).lift)} (F : FrobeniusDiagram p P R D C h)

def frobeniusZero : twistedModules p P R D C ⟶ deltaPresheaf p P R D :=
  whiskerRight F.map (DerivedCategory.homologyFunctor (Modules P.ring) 0) ≫
    (isoWhiskerLeft (deltaPresheaf p P R D)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules P.ring) 0)).hom

def nygaardSubmodule (B : ((Basis p P R)ᵒᵖ)ᵒᵖ) (i : ℕ) :
    Submodule P.ring ((twistedModules p P R D C).obj B) :=
  (P.ideal ^ i • (⊤ : Submodule P.ring ((deltaPresheaf p P R D).obj B))).comap
    ((frobeniusZero p P R D F).app B).hom

theorem map_mem_nygaard {U V : ((Basis p P R)ᵒᵖ)ᵒᵖ} (f : U ⟶ V) (i : ℕ)
    {x : (twistedModules p P R D C).obj U} (hx : x ∈ nygaardSubmodule p P R D F U i) :
    ((twistedModules p P R D C).map f).hom x ∈ nygaardSubmodule p P R D F V i := by
  change ((frobeniusZero p P R D F).app V).hom
    (((twistedModules p P R D C).map f).hom x) ∈
      P.ideal ^ i • (⊤ : Submodule P.ring ((deltaPresheaf p P R D).obj V))
  have hn := congrArg (fun f : (twistedModules p P R D C).obj U ⟶
    (deltaPresheaf p P R D).obj V ↦ f.hom x) ((frobeniusZero p P R D F).naturality f)
  change ((frobeniusZero p P R D F).app V).hom (((twistedModules p P R D C).map f).hom x) =
    ((deltaPresheaf p P R D).map f).hom (((frobeniusZero p P R D F).app U).hom x) at hn
  rw [hn]
  exact Submodule.smul_top_le_comap_smul_top (P.ideal ^ i)
    ((deltaPresheaf p P R D).map f).hom hx

def nygaardPresheaf (i : ℕ) : ((Basis p P R)ᵒᵖ)ᵒᵖ ⥤ Modules P.ring where
  obj B := ModuleCat.of P.ring (nygaardSubmodule p P R D F B i)
  map f := ModuleCat.ofHom
    { toFun x := ⟨((twistedModules p P R D C).map f).hom x.val,
        map_mem_nygaard p P R D F f i x.property⟩
      map_add' x y := Subtype.ext (map_add _ x.val y.val)
      map_smul' a x := Subtype.ext (((twistedModules p P R D C).map f).hom.map_smul a x.val) }
  map_id B := by
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : (twistedModules p P R D C).obj B ⟶
      (twistedModules p P R D C).obj B ↦ f.hom x.val)
      ((twistedModules p P R D C).map_id B)
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun f : (twistedModules p P R D C).obj U ⟶
      (twistedModules p P R D C).obj W ↦ f.hom x.val)
      ((twistedModules p P R D C).map_comp f g)

def inclusion (i : ℕ) : nygaardPresheaf p P R D F i ⟶ twistedModules p P R D C where
  app B := ModuleCat.ofHom (nygaardSubmodule p P R D F B i).subtype
  naturality {U V} f := by ext x; rfl

theorem nygaard_antitone (B : ((Basis p P R)ᵒᵖ)ᵒᵖ) {i j : ℕ} (hij : i ≤ j) :
    nygaardSubmodule p P R D F B j ≤ nygaardSubmodule p P R D F B i :=
  Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hij))

def stepPresheaf (i : ℕ) :
    nygaardPresheaf p P R D F (i + 1) ⟶ nygaardPresheaf p P R D F i where
  app B := ModuleCat.ofHom
    (Submodule.inclusion (nygaard_antitone p P R D F B (Nat.le_succ i)))
  naturality {U V} f := by ext x; rfl

instance moduleSheafify : HasSheafify (topology p P R) (Modules P.ring) := by
  let : HasLimits (Modules P.ring) := ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (Modules P.ring) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} P.ring
  let : PreservesFilteredColimits (forget (Modules P.ring)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (Modules P.ring) AddCommGrpCat.{1}) (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1} (forget (Modules P.ring)) := inferInstance
  infer_instance

abbrev Sheaves := Sheaf (topology p P R) (Modules P.ring)

def deltaSheaf : Sheaves p P R :=
  (presheafToSheaf (topology p P R) _).obj (deltaPresheaf p P R D)

def twistedSheaf (C : Completion P.ring (completionIdeal p P.ideal)) : Sheaves p P R :=
  (presheafToSheaf (topology p P R) _).obj (twistedModules p P R D C)

def nygaardSheaf (i : ℕ) : Sheaves p P R :=
  (presheafToSheaf (topology p P R) _).obj (nygaardPresheaf p P R D F i)

def canSheaf (i : ℕ) : nygaardSheaf p P R D F i ⟶ twistedSheaf p P R D C :=
  (presheafToSheaf (topology p P R) _).map (inclusion p P R D F i)

def stepSheaf (i : ℕ) : nygaardSheaf p P R D F (i + 1) ⟶ nygaardSheaf p P R D F i :=
  (presheafToSheaf (topology p P R) _).map (stepPresheaf p P R D F i)

def frobeniusSheaf : twistedSheaf p P R D C ⟶ deltaSheaf p P R D :=
  (presheafToSheaf (topology p P R) _).map (frobeniusZero p P R D F)

instance sectionLimits : HasLimitsOfShape ((Basis p P R)ᵒᵖ)ᵒᵖ (Modules P.ring) := by
  let : HasLimitsOfSize.{0, 1} (Modules P.ring) := ModuleCat.hasLimitsOfSize.{0, 1, 1, 0}
  infer_instance

def sections : Sheaves p P R ⥤ Modules P.ring :=
  sheafToPresheaf (topology p P R) _ ⋙ lim.{0, 1, 1, 2}

instance sections_additive : (sections p P R).Additive where
  map_add {M N} f g := by
    apply limit.hom_ext
    intro B
    change limMap (f.hom + g.hom) ≫ limit.π N.obj B =
      (limMap f.hom + limMap g.hom) ≫ limit.π N.obj B
    rw [Preadditive.add_comp]
    simp

def sectionsSource : CochainComplex (Sheaves p P R) ℤ ⥤ DerivedCategory (Modules P.ring) :=
  (sections p P R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

class HasDerivedSections : Prop where
  exists_derived : (sectionsSource p P R).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaves p P R) (ComplexShape.up ℤ))

attribute [instance] HasDerivedSections.exists_derived

def derivedSections [HasDerivedSections p P R] : DerivedCategory (Sheaves p P R) ⥤ DerivedCategory (Modules P.ring) :=
  (sectionsSource p P R).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaves p P R) (ComplexShape.up ℤ))

def delta [HasDerivedSections p P R] : DerivedCategory (Modules P.ring) :=
  (derivedSections p P R).obj
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).obj (deltaSheaf p P R D))

def twisted (C : Completion P.ring (completionIdeal p P.ideal))
    [HasDerivedSections p P R] : DerivedCategory (Modules P.ring) :=
  (derivedSections p P R).obj
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).obj (twistedSheaf p P R D C))

def frobeniusGlobal [HasDerivedSections p P R] :
    twisted p P R D C ⟶ delta p P R D :=
  (derivedSections p P R).map
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).map (frobeniusSheaf p P R D F))

def nygaard [HasDerivedSections p P R] (i : ℕ) : DerivedCategory (Modules P.ring) :=
  (derivedSections p P R).obj
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).obj (nygaardSheaf p P R D F i))

def can [HasDerivedSections p P R] (i : ℕ) :
    nygaard p P R D F i ⟶ twisted p P R D C :=
  (derivedSections p P R).map
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).map (canSheaf p P R D F i))

def step [HasDerivedSections p P R] (i : ℕ) :
    nygaard p P R D F (i + 1) ⟶ nygaard p P R D F i :=
  (derivedSections p P R).map
    ((DerivedCategory.singleFunctor (Sheaves p P R) 0).map (stepSheaf p P R D F i))

def nygaardSigned [HasDerivedSections p P R] (i : ℤ) : DerivedCategory (Modules P.ring) :=
  if i ≤ 0 then twisted p P R D C else nygaard p P R D F i.toNat

def canSigned [HasDerivedSections p P R] (i : ℤ) :
    nygaardSigned p P R D F i ⟶ twisted p P R D C := by
  unfold nygaardSigned
  split_ifs with hi
  · exact 𝟙 _
  · exact can p P R D F i.toNat

/-- Full graded cochains, including positive cohomological degrees. -/
def graded [HasDerivedSections p P R] (i : ℕ) : DerivedCategory (Modules P.ring) :=
  (derivedSections p P R).obj (DerivedCategory.Q.obj
    (CochainComplex.mappingCone
      ((HomologicalComplex.single (Sheaves p P R) (ComplexShape.up ℤ) 0).map
        (stepSheaf p P R D F i))))

end MathlibExt.AlgebraicGeometry.RelativeQuasiSyntomicNygaard
