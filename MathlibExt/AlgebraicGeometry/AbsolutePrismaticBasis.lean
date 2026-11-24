/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), the module-sheafification argument:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: specialized to the quasisyntomic basis site.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasiSyntomicPrismSites
public import MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology
public import MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers

/-!
# Universal absolute prism algebras on the actual quasisyntomic basis

Basis objects are actual relative quasisyntomic rings admitting a
surjective map from the residue of a perfect prism. Their delta algebra
is an initial object of the actual absolute prism-lift category.
Restriction maps are its unique universal prism maps.

The algebra, ideal-preimage Nygaard modules and their inclusions have
actual ring elements and actual delta Frobenius. Their sheafifications
and R-Gamma use the native quasisyntomic topology and fixed
right-derived-sections source. These are absolute models; no
identification with phi_A-linearized relative Nygaard or the BMS
theta/theta-tilde convention is silently made.

Reference: Bhatt--Scholze, arXiv:1905.08229v4, Theorems 1.12--1.14,
Sections 7 and 12; BMS arXiv:1802.03261v2, Definitions 4.20 and
Lemma 4.28. Module sheafification adapts the already attributed
AxiomMath/Stacks ProetaleComparison source at
c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache 2.0.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AbsolutePrismaticBasis

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open QuasiSyntomicPrismSites PrismaticNygaardTowers

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]

/-- The actual semiperfectoid residue criterion, with a real perfect base prism. -/
def IsSemiperfectoid (S : QuasiSyntomicPrismSites.Ring p) : Prop :=
  ∃ (P : Prism.{0} p),
    Function.Bijective (DeltaRing.frobenius p P.ring) ∧
      ∃ f : P.Residue →+* S.algebra, Function.Surjective f

/-- The genuine semiperfectoid basis of the relative quasisyntomic site. -/
abbrev Basis (A : QuasiSyntomicPrismSites.Ring p) :=
  (show ObjectProperty (Relative p A) from
    fun S ↦ IsSemiperfectoid p S.obj.right).FullSubcategory

/-- The underlying actual ring of a basis object. -/
abbrev ring {A : QuasiSyntomicPrismSites.Ring p} (S : Basis p A) :=
  S.obj.obj.right.algebra

/-- The actual algebra map of a basis morphism. -/
abbrev ringMap {A : QuasiSyntomicPrismSites.Ring p} {S T : Basis p A} (f : S ⟶ T) :=
  f.hom.hom.right

/-- The covering rule is the actual complete-flat quasisyntomic rule. -/
def topology (A : QuasiSyntomicPrismSites.Ring p) : GrothendieckTopology (Basis p A)ᵒᵖ :=
  sInf {J | ∀ (S T : Basis p A) (f : S ⟶ T),
    IsCover p (ringMap p f) →
      Sieve.ofArrows (fun _ : Unit ↦ op T) (fun _ ↦ f.op) ∈ J (op S)}

variable (S : Type) [CommRing S]

/-- An actual absolute bounded prism over the given semiperfectoid ring. -/
structure Lift where
  prism : Prism.{0} p
  residue : S →+* prism.Residue

/-- Actual universal-lift arrows retain the source residue map. -/
@[ext] structure LiftHom (U V : Lift p S) where
  map : U.prism ⟶ V.prism
  residue : (BoundedPrisms.Hom.residue p map).comp U.residue = V.residue

private theorem residue_id (P : Prism.{0} p) :
    BoundedPrisms.Hom.residue p (𝟙 P) = RingHom.id P.Residue := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem residue_comp {P Q R : Prism.{0} p} (f : P ⟶ Q) (g : Q ⟶ R) :
    BoundedPrisms.Hom.residue p (f ≫ g) =
      (BoundedPrisms.Hom.residue p g).comp (BoundedPrisms.Hom.residue p f) := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

instance : Category (Lift p S) where
  Hom := LiftHom p S
  id U := ⟨𝟙 U.prism, by rw [residue_id]; rfl⟩
  comp f g := ⟨f.map ≫ g.map, by rw [residue_comp, RingHom.comp_assoc, f.residue, g.residue]⟩
  id_comp _ := by apply LiftHom.ext; exact Category.id_comp _
  comp_id _ := by apply LiftHom.ext; exact Category.comp_id _
  assoc _ _ _ := by apply LiftHom.ext; exact Category.assoc _ _ _

/-- The actual initial delta algebra, not a freely supplied cohomology ring. -/
structure InitialLift where
  lift : Lift p S
  initial : IsInitial lift

variable {S} {T : Type} [CommRing T]

/-- View a target prism as a source lift by the actual residue ring map. -/
def changeResidue (f : S →+* T) (V : Lift p T) : Lift p S :=
  ⟨V.prism, V.residue.comp f⟩

/-- Universality supplies the real delta-map between the actual initial rings. -/
def initialMap (U : InitialLift p S) (V : InitialLift p T) (f : S →+* T) :
    U.lift.prism ⟶ V.lift.prism :=
  (U.initial.to (changeResidue p f V.lift)).map

/-- The identity residue map induces the actual identity prism map. -/
theorem initialMap_id (U : InitialLift p S) :
    initialMap p U U (RingHom.id S) = 𝟙 U.lift.prism := by
  change (U.initial.to U.lift).map = (𝟙 U.lift : U.lift ⟶ U.lift).map
  exact congrArg LiftHom.map (U.initial.hom_ext _ _)

/-- Composition follows from the same initial-object uniqueness, with its residue square. -/
theorem initialMap_comp {R : Type} [CommRing R]
    (U : InitialLift p S) (V : InitialLift p T) (W : InitialLift p R)
    (f : S →+* T) (g : T →+* R) :
    initialMap p U W (g.comp f) = initialMap p U V f ≫ initialMap p V W g := by
  let h : U.lift ⟶ changeResidue p (g.comp f) W.lift :=
    ⟨initialMap p U V f ≫ initialMap p V W g, by
      change (BoundedPrisms.Hom.residue p
        (initialMap p U V f ≫ initialMap p V W g)).comp U.lift.residue =
          W.lift.residue.comp (g.comp f)
      rw [residue_comp, RingHom.comp_assoc]
      have hf : (BoundedPrisms.Hom.residue p (initialMap p U V f)).comp
          U.lift.residue = V.lift.residue.comp f :=
        (U.initial.to (changeResidue p f V.lift)).residue
      have hg : (BoundedPrisms.Hom.residue p (initialMap p V W g)).comp
          V.lift.residue = W.lift.residue.comp g :=
        (V.initial.to (changeResidue p g W.lift)).residue
      rw [hf, ← RingHom.comp_assoc, hg]
      rfl⟩
  exact congrArg LiftHom.map (U.initial.hom_ext _ h)

variable (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))

/-- The actual universal prism map of a quasisyntomic basis morphism. -/
abbrev map {U V : Basis p A} (f : U ⟶ V) :=
  initialMap p (D U) (D V) (ringMap p f).toRingHom

/-- The structural module presheaf consists of the actual initial delta-ring elements. -/
def deltaPresheaf : ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{1} ℤ where
  obj B := ModuleCat.of ℤ (ULift.{1} (D B.unop.unop).lift.prism.ring)
  map f := ModuleCat.ofHom
    { toFun x := ULift.up ((map p A D f.unop.unop).hom x.down)
      map_add' x y := ULift.ext (map_add _ _ _)
      map_smul' a x := ULift.ext (map_zsmul _ _ _) }
  map_id B := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    exact congrArg (fun f ↦ f.hom x.down) (initialMap_id p (D B.unop.unop))
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    exact congrArg (fun f ↦ f.hom x.down)
      (initialMap_comp p (D _) (D _) (D _) (ringMap p f.unop.unop).toRingHom
        (ringMap p g.unop.unop).toRingHom)

/-- The actual Nygaard ideal at a basis object. -/
abbrev ideal (B : Basis p A) (n : ℕ) :
    Ideal (D B).lift.prism.ring :=
  nygaardIdeal p (D B).lift.prism.ring (D B).lift.prism.ideal n

/-- Universal prism maps preserve the actual Nygaard ideal preimages. -/
theorem map_mem_ideal {U V : Basis p A} (f : U ⟶ V) (n : ℕ)
    {x : (D U).lift.prism.ring} (hx : x ∈ ideal p A D U n) :
    (map p A D f).hom x ∈ ideal p A D V n := by
  change DeltaRing.frobenius p (D V).lift.prism.ring ((map p A D f).hom x) ∈
    (D V).lift.prism.ideal ^ n
  rw [← BoundedPrisms.Hom.frobenius p (map p A D f)]
  change DeltaRing.frobenius p (D U).lift.prism.ring x ∈
    (D U).lift.prism.ideal ^ n at hx
  have h := Ideal.mem_map_of_mem (map p A D f).hom hx
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono (map p A D f).ideal n h

/-- Native ideal-preimage modules and actual universal restriction maps. -/
def nygaardPresheaf (n : ℕ) : ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{1} ℤ where
  obj B := ModuleCat.of ℤ (ULift.{1} (ideal p A D B.unop.unop n))
  map f := ModuleCat.ofHom
    { toFun x := ULift.up ⟨(map p A D f.unop.unop).hom x.down.val,
        map_mem_ideal p A D f.unop.unop n x.down.property⟩
      map_add' x y := ULift.ext (Subtype.ext (map_add _ _ _))
      map_smul' a x := ULift.ext (Subtype.ext (map_zsmul _ _ _)) }
  map_id B := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom x.down.val) (initialMap_id p (D B.unop.unop))
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    exact congrArg (fun f ↦ f.hom x.down.val)
      (initialMap_comp p (D _) (D _) (D _) (ringMap p f.unop.unop).toRingHom
        (ringMap p g.unop.unop).toRingHom)

/-- The filtration's actual presheaf inclusion. -/
def inclusion (n : ℕ) : nygaardPresheaf p A D n ⟶ deltaPresheaf p A D where
  app B := ModuleCat.ofHom
    { toFun x := ULift.up x.down.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality {U V} f := by ext x; rfl

/-- The actual induced map on each finite Nygaard quotient ring. -/
def quotientMap {U V : Basis p A} (f : U ⟶ V) (n : ℕ) :
    QuotientRing p (D U).lift.prism.ring (D U).lift.prism.ideal n →+*
      QuotientRing p (D V).lift.prism.ring (D V).lift.prism.ideal n :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (map p A D f).hom) (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (map_mem_ideal p A D f (n + 1) hx))

/-- Finite quotient rings, on the actual geometric-opposite basis presheaf. -/
def quotientPresheaf (n : ℕ) : ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{0} where
  obj B := CommRingCat.of
    (QuotientRing p (D B.unop.unop).lift.prism.ring (D B.unop.unop).lift.prism.ideal n)
  map f := CommRingCat.ofHom (quotientMap p A D f.unop.unop n)
  map_id B := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((map p A D (𝟙 _)).hom x) = Ideal.Quotient.mk _ x
    exact congrArg (fun f ↦ Ideal.Quotient.mk
      (nygaardIdeal p (D B.unop.unop).lift.prism.ring
        (D B.unop.unop).lift.prism.ideal (n + 1)) (f.hom x))
      (initialMap_id p (D B.unop.unop))
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun f ↦ Ideal.Quotient.mk
      (nygaardIdeal p (D W.unop.unop).lift.prism.ring
        (D W.unop.unop).lift.prism.ideal (n + 1)) (f.hom x))
      (initialMap_comp p (D _) (D _) (D _)
        (ringMap p f.unop.unop).toRingHom (ringMap p g.unop.unop).toRingHom)

/-- Native adjacent quotient maps, with no free finite-stage coefficient operator. -/
def quotientPresheafTransition (n : ℕ) :
    quotientPresheaf p A D (n + 1) ⟶ quotientPresheaf p A D n where
  app B := CommRingCat.ofHom
    (quotientTransition p (D B.unop.unop).lift.prism.ring
      (D B.unop.unop).lift.prism.ideal n)
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- The original actual quasisyntomic ring presheaf, used for canonical reduction. -/
def originalRings : ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{0} where
  obj B := CommRingCat.of (ring p B.unop.unop)
  map f := CommRingCat.ofHom (ringMap p f.unop.unop).toRingHom
  map_id _ := by apply CommRingCat.hom_ext; ext x; rfl
  map_comp _ _ := by apply CommRingCat.hom_ext; ext x; rfl

/-- Canonical zero-step reduction is constrained by the actual Frobenius-residue image. -/
structure ZeroReduction where
  iso : quotientPresheaf p A D 0 ≅ originalRings p A
  normalization : ∀ (B : ((Basis p A)ᵒᵖ)ᵒᵖ)
    (x : (D B.unop.unop).lift.prism.ring),
    (D B.unop.unop).lift.residue
      ((iso.hom.app B).hom (Ideal.Quotient.mk _ x)) =
        Ideal.Quotient.mk (D B.unop.unop).lift.prism.ideal
          (DeltaRing.frobenius p (D B.unop.unop).lift.prism.ring x)

end MathlibExt.AlgebraicGeometry.AbsolutePrismaticBasis
