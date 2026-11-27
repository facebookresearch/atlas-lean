/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardCohomology
public import MathlibExt.AlgebraicGeometry.PrismaticBreuilKisinSeeds
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Actual finite Nygaard-quotient lines and signed filtered twist complexes

Finite coefficient rings are the actual initial-prism Nygaard quotients.
A line and its dual are genuine presheaves of modules over those rings,
with native tensor evaluation, finite-quotient inverse and a normalized
zero-step reduction. Signed powers use the actual tensor word of the
line or its actual dual.

Perfectoid-base normalization uses the literal p-divided conormal seed.
The coefficient map explicitly includes inverse phi_A before the
initial-prism map; its reduction is the seed's theta reduction. This
records the BMS/relative-prism scalar convention as real map data.

The completed twist is the native Milnor fiber of the actual adjacent
line quotients. Positive Nygaard steps are its quotient-projection
fibers. No inverse of an unfiltered inverse-limit object is inferred.

References: BMS arXiv:1802.03261v2, Theorem 1.12(3), footnote 3,
Proposition 6.5 and Section 7.4; BMS18 arXiv:1602.03148v3,
Example 4.24. Construction and source-normalization providers remain
direct Wanted outputs.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticFilteredTwists

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor Opposite
open AbsolutePrismaticBasis
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open PrismaticBreuilKisinSeeds
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

local instance integerAllLimits : HasLimitsOfSize.{1, 1} (ModuleCat.{1} ℤ) :=
  ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}

local instance integerSmallLimits : HasLimitsOfSize.{0, 0} (ModuleCat.{1} ℤ) :=
  ModuleCat.hasLimitsOfSize.{0, 0, 1, 0}

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))

/-- Actual finite-quotient module presheaves, in the coefficient-ring universe. -/
abbrev Modules (n : ℕ) :=
  PresheafOfModulesOfCommRing.{0} (quotientPresheaf p A D n)

/-- Native coefficient restriction for the real adjacent quotient-ring map. -/
def restrict (n : ℕ) : Modules p A D n ⥤ Modules p A D (n + 1) :=
  PresheafOfModules.restrictScalars
    (whiskerRight (quotientPresheafTransition p A D n)
      (forget₂ CommRingCat.{0} RingCat.{0}))

/-- Integer modules keep the actual additive maps of a module presheaf. -/
def integerModules : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℤ where
  obj G := ModuleCat.of ℤ G
  map f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := _root_.map_add _
      map_smul' a x := _root_.map_zsmul f.hom a x }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The native integer presheaf functor on any actual ringed site. -/
def integerPresheaves {C : Type 1} [Category.{0} C] (R : Cᵒᵖ ⥤ RingCat.{0}) :
    PresheafOfModules.{0} R ⥤ Cᵒᵖ ⥤ ModuleCat.{1} ℤ :=
  PresheafOfModules.toPresheaf R ⋙
    (Functor.whiskeringRight _ _ _).obj
      (integerModules ⋙ ModuleCat.uliftFunctor.{1, 0} ℤ)

/-- Native scalar-restriction comparison, before specializing any coefficient rings. -/
def integerRestrictionIso {C : Type 1} [Category.{0} C]
    {R S : Cᵒᵖ ⥤ RingCat.{0}} (f : R ⟶ S) :
    PresheafOfModules.restrictScalars f ⋙ integerPresheaves R ≅ integerPresheaves S :=
  isoWhiskerRight (PresheafOfModules.restrictScalarsCompToPresheaf f)
    ((Functor.whiskeringRight _ _ _).obj
      (integerModules ⋙ ModuleCat.uliftFunctor.{1, 0} ℤ))

/-- The fixed underlying integer presheaf, with only a universe lift. -/
def integers (n : ℕ) :
    Modules p A D n ⥤ ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{1} ℤ :=
  integerPresheaves (quotientPresheaf p A D n ⋙ forget₂ _ RingCat.{0})

/-- Restriction of ring scalars leaves the underlying integer presheaf unchanged. -/
def restrictIntegersIso (n : ℕ) :
    restrict p A D n ⋙ integers p A D (n + 1) ≅ integers p A D n :=
  integerRestrictionIso (whiskerRight (quotientPresheafTransition p A D n)
    (forget₂ CommRingCat.{0} RingCat.{0}))

variable {C : Type 1} [Category.{0} C]
  (O : Cᵒᵖ ⥤ CommRingCat.{0})

/-- The literal native tensor word in a coefficient-module presheaf category. -/
def word (M : PresheafOfModulesOfCommRing.{0} O) :
    ℕ → PresheafOfModulesOfCommRing.{0} O
  | 0 => 𝟙_ _
  | n + 1 => M ⊗ word M n

/-- Actual homogeneous pure tensor generators at an actual site object. -/
def wordGenerator (M : PresheafOfModulesOfCommRing.{0} O) (X : Cᵒᵖ) :
    (n : ℕ) → (Fin n → M.obj X) → (word O M n).obj X
  | 0, _ => (1 : O.obj X)
  | n + 1, x => (x 0) ⊗ₜ[O.obj X]
      wordGenerator M X n (fun j ↦ x j.succ)

/-- Signed weights distinguish every negative integer and use the actual dual word. -/
def signedWord (M N : PresheafOfModulesOfCommRing.{0} O) :
    ℤ → PresheafOfModulesOfCommRing.{0} O
  | Int.ofNat n => word O M n
  | Int.negSucc n => word O N (n + 1)

variable {O}

/-- The actual initial-prism scalar map coming from a perfectoid residue map. -/
def perfectoidBaseMap (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (P : Prism.{0} p)
    (initial : IsInitial ({ prism := P, residue := RingHom.id P.Residue } : Lift p P.Residue))
    (f : P.Residue →+* ring p B.unop.unop) :
    P ⟶ (D B.unop.unop).lift.prism :=
  initialMap p ⟨{ prism := P, residue := RingHom.id _ }, initial⟩ (D B.unop.unop) f

/-- The finite coefficient map includes the real inverse-Frobenius scalar transport. -/
def adjustedScalars (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (P : Prism.{0} p)
    (perfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (initial : IsInitial ({ prism := P, residue := RingHom.id P.Residue } : Lift p P.Residue))
    (f : P.Residue →+* ring p B.unop.unop) (n : ℕ) :
    P.ring →+* (quotientPresheaf p A D n).obj B :=
  (Ideal.Quotient.mk _).comp
    ((perfectoidBaseMap p A D B P initial f).hom.comp
      (RingEquiv.ofBijective (DeltaRing.frobenius p P.ring) perfect).symm.toRingHom)

/-- Perfectoid-base comparison data on the actual finite line carriers. -/
structure ClassicalMatch
    (Z : ZeroReduction p A D)
    (line : ∀ n : ℕ, Modules p A D n)
    (reduction : line 0 ≅ 𝟙_ (Modules p A D 0))
    (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (P : Prism.{0} p)
    (perfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (initial : IsInitial ({ prism := P, residue := RingHom.id P.Residue } : Lift p P.Residue))
    (f : P.Residue →+* ring p B.unop.unop) (L : ClassicalSeed p P) where
  comparison : ∀ n : ℕ, (line n).obj B ≅
    (ModuleCat.extendScalars (adjustedScalars p A D B P perfect initial f n)).obj L.module
  theta_reduction : ∀ x : L.module,
    (Z.iso.hom.app B).hom
      ((reduction.hom.app B).hom
        ((comparison 0).inv
          (((ModuleCat.extendRestrictScalarsAdj
            (adjustedScalars p A D B P perfect initial f 0)).unit.app L.module).hom x))) =
      f (L.reduction.reduction x)

/-- Finite filtered Breuil--Kisin line data, with all inverses confined to finite quotients.
All module/ring maps and point evaluations are native; these are construction outputs. -/
structure FiniteLineTower {C : Type 1} [Category.{0} C]
    (coeff : ℕ → Cᵒᵖ ⥤ CommRingCat.{0})
    (q : ∀ n : ℕ, coeff (n + 1) ⟶ coeff n) (J : GrothendieckTopology C) where
  line : ∀ n : ℕ, PresheafOfModulesOfCommRing.{0} (coeff n)
  dual : ∀ n : ℕ, PresheafOfModulesOfCommRing.{0} (coeff n)
  dualPoint : ∀ (n : ℕ) (B : Cᵒᵖ), (dual n).obj B ≅
    ModuleCat.of ((coeff n).obj B)
      (Module.Dual ((coeff n).obj B) ((line n).obj B))
  evaluation : ∀ n : ℕ, dual n ⊗ line n ≅ 𝟙_ (PresheafOfModulesOfCommRing.{0} (coeff n))
  evaluation_point : ∀ (n : ℕ) (B : Cᵒᵖ)
    (f : (dual n).obj B) (x : (line n).obj B),
    ((evaluation n).hom.app B).hom (f ⊗ₜ[(coeff n).obj B] x) =
      ((dualPoint n B).hom f) x
  reduction : line 0 ≅ 𝟙_ (PresheafOfModulesOfCommRing.{0} (coeff 0))
  lineTransition : ∀ n : ℕ, line (n + 1) ⟶
    (PresheafOfModules.restrictScalars
      (whiskerRight (q n) (forget₂ _ RingCat.{0}))).obj (line n)
  dualTransition : ∀ n : ℕ, dual (n + 1) ⟶
    (PresheafOfModules.restrictScalars
      (whiskerRight (q n) (forget₂ _ RingCat.{0}))).obj (dual n)
  evaluation_transition : ∀ (n : ℕ) (B : Cᵒᵖ)
    (f : (dual (n + 1)).obj B) (x : (line (n + 1)).obj B),
    ((evaluation n).hom.app B).hom
      (((dualTransition n).app B).hom f ⊗ₜ[(coeff n).obj B]
        ((lineTransition n).app B).hom x) =
      ((q n).app B).hom
        (((evaluation (n + 1)).hom.app B).hom
          (f ⊗ₜ[(coeff (n + 1)).obj B] x))
  transition : ∀ (n : ℕ) (i : ℤ),
    signedWord (coeff (n + 1)) (line (n + 1)) (dual (n + 1)) i ⟶
      (PresheafOfModules.restrictScalars (whiskerRight (q n) (forget₂ _ RingCat.{0}))).obj
        (signedWord (coeff n) (line n) (dual n) i)
  positive_word : ∀ (n k : ℕ) (B : Cᵒᵖ)
    (x : Fin k → (line (n + 1)).obj B),
    ((transition n (Int.ofNat k)).app B).hom
      (wordGenerator (coeff (n + 1)) (line (n + 1)) B k x) =
      wordGenerator (coeff n) (line n) B k
        (fun j ↦ ((lineTransition n).app B).hom (x j))
  negative_word : ∀ (n k : ℕ) (B : Cᵒᵖ)
    (x : Fin (k + 1) → (dual (n + 1)).obj B),
    ((transition n (Int.negSucc k)).app B).hom
      (wordGenerator (coeff (n + 1)) (dual (n + 1)) B (k + 1) x) =
      wordGenerator (coeff n) (dual n) B (k + 1)
        (fun j ↦ ((dualTransition n).app B).hom (x j))
  sheaf : ∀ (n : ℕ) (i : ℤ), Presheaf.IsSheaf J
    ((integerPresheaves (coeff n ⋙ forget₂ _ RingCat.{0})).obj
      (signedWord (coeff n) (line n) (dual n) i))

/-- A finite-quotient line tower on the actual initial-prism coefficients,
with its explicitly source-normalized perfectoid comparisons. -/
structure TwistTower (Z : ZeroReduction p A D) where
  data : FiniteLineTower (fun n ↦ quotientPresheaf p A D n)
    (quotientPresheafTransition p A D) (topology p A)
  classical : ∀ (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (P : Prism.{0} p)
    (perfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (initial : IsInitial ({ prism := P, residue := RingHom.id P.Residue } : Lift p P.Residue))
    (f : P.Residue →+* ring p B.unop.unop) (L : ClassicalSeed p P),
    ClassicalMatch p A D Z data.line data.reduction B P perfect initial f L

namespace TwistTower

variable {p A D} {Z : ZeroReduction p A D} (T : TwistTower p A D Z)

/-- The actual signed finite line presheaf. -/
def finite (n : ℕ) (i : ℤ) : Modules p A D n :=
  signedWord (quotientPresheaf p A D n) (T.data.line n) (T.data.dual n) i

/-- The same real finite line as an integer-coefficient sheaf. -/
def finiteSheaf (n : ℕ) (i : ℤ) : PrismaticNygaardCohomology.Sheaves p A :=
  ⟨(integers p A D n).obj (T.finite n i), T.data.sheaf n i⟩

/-- Adjacent sheaf maps follow actual scalar restriction and the fixed signed tensor maps. -/
def finiteSheafTransition (n : ℕ) (i : ℤ) :
    T.finiteSheaf (n + 1) i ⟶ T.finiteSheaf n i :=
  ⟨(integers p A D (n + 1)).map (T.data.transition n i) ≫
    (restrictIntegersIso p A D n).hom.app (T.finite n i)⟩

/-- Real finite quotient complexes on the actual quasisyntomic site. -/
def levelComplex (i : ℤ) (n : ℕ) :
    CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  (HomologicalComplex.single (PrismaticNygaardCohomology.Sheaves p A)
    (ComplexShape.up ℤ) 0).obj (T.finiteSheaf n i)

/-- Native adjacent cochain maps of these real line quotients. -/
def levelTransition (i : ℤ) (n : ℕ) :
    T.levelComplex i (n + 1) ⟶ T.levelComplex i n :=
  (HomologicalComplex.single (PrismaticNygaardCohomology.Sheaves p A)
    (ComplexShape.up ℤ) 0).map (T.finiteSheafTransition n i)

/-- The actual finite-quotient product, retaining all negative weights. -/
abbrev productComplex (i : ℤ) :
    CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ := ∏ᶜ T.levelComplex i

/-- Its literal Milnor difference. -/
def difference (i : ℤ) : T.productComplex i ⟶ T.productComplex i :=
  Pi.lift (f := T.levelComplex i) (fun n : ℕ ↦ Pi.π (T.levelComplex i) n -
    Pi.π (T.levelComplex i) (n + 1) ≫ T.levelTransition i n)

/-- The actual completed signed twist in cochains of quasisyntomic integer sheaves. -/
def complex (i : ℤ) : CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  CochainComplex.mappingCocone (T.difference i)

/-- The actual finite-quotient projection. -/
def projection (i : ℤ) (n : ℕ) : T.complex i ⟶ T.levelComplex i n :=
  CochainComplex.mappingCocone.fst (T.difference i) ≫ Pi.π (T.levelComplex i) n

/-- A positive completed Nygaard step is the literal fiber of this projection. -/
def positiveNygaard (i : ℤ) (n : ℕ) :
    CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  CochainComplex.mappingCocone (T.projection i n)

/-- Signed Nygaard steps use the whole object at zero and every negative boundary. -/
def nygaard (i : ℤ) : CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  match i with
  | Int.ofNat 0 => T.complex 0
  | Int.ofNat (n + 1) => T.positiveNygaard (n + 1) n
  | Int.negSucc n => T.complex (Int.negSucc n)

/-- The canonical map is the actual fiber inclusion or identity at nonpositive weights. -/
def can (i : ℤ) : T.nygaard i ⟶ T.complex i :=
  match i with
  | Int.ofNat 0 => 𝟙 _
  | Int.ofNat (n + 1) => CochainComplex.mappingCocone.fst (T.projection (n + 1) n)
  | Int.negSucc _ => 𝟙 _

end TwistTower

end MathlibExt.AlgebraicGeometry.PrismaticFilteredTwists
