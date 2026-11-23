/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.MonoidAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationSpectralAction
public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeTotalNaturality
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Actual BK spectral modules and literal signed-total homology

The actual second-translation representation supplies the module-valued
complete-filtration spectral object. Its canonical bottom-relative comparison
at `p = 0`, `q = d` transfers the scalars onto the literal signed-total homology
group. No chain-level monoid action or module comparison is supplied.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian Limits ZeroObject
open HomologicalComplex₂ ComposableArrows

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "A" => MonoidAlgebra ℤ (Multiplicative (Skeleton C))

/-- The module-valued spectral object of the actual complete BK filtration. -/
def secondTranslationBKModuleSpectralObject : SpectralObject (ModuleCat.{u} A) EInt :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModule (secondTranslationBKSpectralAction (C := C) R)

/-- Forgetting scalars recovers the exact original complete BK spectral object. -/
theorem secondTranslationBKModuleSpectralObject_forget :
    SpectralObject.forgetMonoidModule (secondTranslationBKModuleSpectralObject (C := C) R) =
      (horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
          (SSet.rightCommaNerveDiagram (translationProjection (C := C))))) :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).forgetMonoidModule_monoidModule (secondTranslationBKSpectralAction (C := C) R)

/-- The finite canonical bottom-relative abutment interval in total degree `d`. -/
abbrev secondTranslationBKAbutmentInterval (d : ℕ) : ComposableArrows EInt 1 :=
  mk₁ (horizontalCanonicalAbutmentTotalMap 0 d)

/-- The actual module on the canonical bottom-relative interval group. -/
def secondTranslationBKAbutmentIntervalModule (d : ℕ) : ModuleCat.{u} A :=
  ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).monoidModuleInterval (secondTranslationBKSpectralAction (C := C) R)
    (-(d : ℤ)) (secondTranslationBKAbutmentInterval d)

/-- The original canonical comparison at `p = 0`, `q = d`, with literal
signed-total homology as its target. -/
def secondTranslationBKBottomRelativeToTotalIso (d : ℕ) :
    (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).obj (secondTranslationBKAbutmentInterval d) ≅
      (((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).total (ComplexShape.down ℕ)).homology d := by
  simpa only [Nat.zero_add] using horizontalBottomRelativeHomologyToTotalIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) 0 d

private theorem castIso_hom {D : Type*} [Category* D] {X Y X' Y' : D}
    (e : X ≅ Y) (hX : X = X') (hY : Y = Y') (h : (X ≅ Y) = (X' ≅ Y')) :
    (cast h e).hom = eqToHom hX.symm ≫ e.hom ≫ eqToHom hY := by
  cases hX
  cases hY
  simp

private theorem secondTranslationBKBottomRelativeToTotalIso_hom (d : ℕ) :
    (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom =
      (horizontalBottomRelativeHomologyStageIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (horizontalAbutmentUpperIndex 0 d) d).hom ≫
        horizontalCompleteHomologyToTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) d (horizontalAbutmentUpperIndex 0 d) := by
  dsimp only [secondTranslationBKBottomRelativeToTotalIso]
  erw [castIso_hom _ (by simp only [Nat.zero_add]) (by simp only [Nat.zero_add])]
  simp only [horizontalBottomRelativeHomologyToTotalIso,
    horizontalAbutmentUpperHomologyToTotalIso, Iso.trans_hom, asIso_hom]
  simpa only [Category.assoc] using
    (dcongr_arg (fun k : ℕ =>
      (horizontalBottomRelativeHomologyStageIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (horizontalAbutmentUpperIndex 0 d) k).hom ≫
        horizontalCompleteHomologyToTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) k (horizontalAbutmentUpperIndex 0 d))
      (Nat.zero_add d).symm).symm

/-- The additive canonical comparison from the constructed interval module
to the exact original total-homology group. -/
def secondTranslationBKBottomRelativeToTotalAddEquiv (d : ℕ) :
    secondTranslationBKAbutmentIntervalModule (C := C) R d ≃+
      (((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).total (ComplexShape.down ℕ)).homology d :=
  ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
    (-(d : ℤ)) (secondTranslationBKAbutmentInterval d)).asModuleEquiv.toAddEquiv).trans
      (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).addCommGroupIsoToAddEquiv

/-- Integral class-monoid scalars on the literal signed-total homology group,
constructed through the inverse canonical additive comparison. -/
def secondTranslationBKTotalHomologyModule (d : ℕ) : ModuleCat.{u} A :=
  letI := (secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d).symm.module A
  ModuleCat.of A ((((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).total (ComplexShape.down ℕ)).homology d)

/-- The canonical bottom-relative comparison is linear for the constructed
scalars on the literal target group. -/
def secondTranslationBKBottomRelativeToTotalLinearEquiv (d : ℕ) :
    secondTranslationBKAbutmentIntervalModule (C := C) R d ≃ₗ[A]
      secondTranslationBKTotalHomologyModule (C := C) R d :=
  ((secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d).symm.linearEquiv A).symm

/-- The additive comparison has exactly the original canonical underlying map. -/
@[simp]
theorem secondTranslationBKBottomRelativeToTotalAddEquiv_apply (d : ℕ)
    (x : secondTranslationBKAbutmentIntervalModule (C := C) R d) :
    secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d x =
      (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom
        ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
          (-(d : ℤ)) (secondTranslationBKAbutmentInterval d)).asModuleEquiv x) := rfl

/-- The linear comparison retains that same canonical additive map. -/
@[simp]
theorem secondTranslationBKBottomRelativeToTotalLinearEquiv_apply (d : ℕ)
    (x : secondTranslationBKAbutmentIntervalModule (C := C) R d) :
    secondTranslationBKBottomRelativeToTotalLinearEquiv (C := C) R d x =
      secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d x := rfl

/-- Bicomplex naturality identifies the original signed-total translation
with the transported interval translation. -/
theorem secondTranslationBKBottomRelativeToTotal_intertwines (d : ℕ) (B : C)
    (x : (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).obj (secondTranslationBKAbutmentInterval d)) :
    (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom
        (((secondTranslationBKSpectralMap R B).asHom.hom (-(d : ℤ))).app
          (secondTranslationBKAbutmentInterval d) x) =
      HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R B) d
        ((secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom x) := by
  have h := horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (secondTranslationBKBicomplexMap R B) 0 d
  have h' : ((secondTranslationBKSpectralMap R B).asHom.hom (-(d : ℤ))).app
      (secondTranslationBKAbutmentInterval d) ≫
        (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom =
      (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom ≫
        HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R B) d := by
    rw [secondTranslationBKBottomRelativeToTotalIso_hom]
    convert h using 1 <;>
      dsimp only [secondTranslationBKSpectralMap, secondTranslationBKAbutmentInterval,
      horizontalBottomRelativeHomologyToTotalIso, horizontalAbutmentUpperHomologyToTotalIso,
      Iso.trans_hom, asIso_hom] <;>
      congr! <;> simp
  exact ConcreteCategory.congr_hom h' x

/-- Every integral class monomial acts on the literal target by the original
signed-total second-translation map with that integer coefficient. -/
theorem secondTranslationBKTotalHomologyModule_single_apply (d : ℕ) (B : C) (z : ℤ)
    (x : secondTranslationBKTotalHomologyModule (C := C) R d) :
    MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton B)) z • x =
      z • HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R B) d x := by
  let e := secondTranslationBKBottomRelativeToTotalLinearEquiv (C := C) R d
  obtain ⟨y, rfl⟩ := e.surjective x
  change (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
    (-(d : ℤ)) (secondTranslationBKAbutmentInterval d)).asModule at y
  rw [← e.map_smul]
  change secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d
      (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton B)) z • y) =
    z • HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R B) d
      (secondTranslationBKBottomRelativeToTotalAddEquiv (C := C) R d y)
  rw [secondTranslationBKBottomRelativeToTotalAddEquiv_apply,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single]
  simp only [LinearMap.smul_apply]
  rw [map_zsmul]
  congr 1
  change (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom
      (((secondTranslationBKSpectralAction (C := C) R
        (Multiplicative.ofAdd (toSkeleton B))).asHom.hom (-(d : ℤ))).app
          (secondTranslationBKAbutmentInterval d)
            ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
              (-(d : ℤ)) (secondTranslationBKAbutmentInterval d)).asModuleEquiv y)) = _
  rw [secondTranslationBKSpectralAction_toSkeleton]
  exact secondTranslationBKBottomRelativeToTotal_intertwines R d B _

/-- The actual bottom-relative interval at an arbitrary extended filtration cut. -/
abbrev secondTranslationBKStageInterval (i : EInt) : ComposableArrows EInt 1 :=
  mk₁ (horizontalBottomToStageMap i)

/-- The module on the original bottom-relative homology of an arbitrary stage. -/
abbrev secondTranslationBKStageIntervalModule (d : ℕ) (i : EInt) : ModuleCat.{u} A :=
  ((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).obj
    (secondTranslationBKStageInterval i)

/-- The canonical additive comparison with literal complete-stage homology. -/
def secondTranslationBKStageAddEquiv (d : ℕ) (i : EInt) :
    secondTranslationBKStageIntervalModule (C := C) R d i ≃+
      (horizontalCompleteFilteredTotalComplex (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i).homology d :=
  ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
    (-(d : ℤ)) (secondTranslationBKStageInterval i)).asModuleEquiv.toAddEquiv).trans
      (horizontalBottomRelativeHomologyStageIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i d).addCommGroupIsoToAddEquiv

/-- Scalars on the literal homology group of every complete stage, including
bottom, negative cuts and top. -/
def secondTranslationBKStageHomologyModule (d : ℕ) (i : EInt) : ModuleCat.{u} A :=
  letI := (secondTranslationBKStageAddEquiv (C := C) R d i).symm.module A
  ModuleCat.of A ((horizontalCompleteFilteredTotalComplex (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i).homology d)

/-- The actual bottom-relative/stage comparison with its constructed linearity. -/
def secondTranslationBKStageLinearEquiv (d : ℕ) (i : EInt) :
    secondTranslationBKStageIntervalModule (C := C) R d i ≃ₗ[A]
      secondTranslationBKStageHomologyModule (C := C) R d i :=
  ((secondTranslationBKStageAddEquiv (C := C) R d i).symm.linearEquiv A).symm

/-- The corresponding canonical isomorphism of actual module objects. -/
def secondTranslationBKStageModuleIso (d : ℕ) (i : EInt) :
    secondTranslationBKStageIntervalModule (C := C) R d i ≅
      secondTranslationBKStageHomologyModule (C := C) R d i :=
  (secondTranslationBKStageLinearEquiv (C := C) R d i).toModuleIso

/-- The actual interval morphism induced by an inequality of complete cuts. -/
def secondTranslationBKStageIntervalMap {i j : EInt} (h : i ≤ j) :
    secondTranslationBKStageInterval i ⟶ secondTranslationBKStageInterval j :=
  twoδ₂Toδ₁ (horizontalBottomToStageMap i) (homOfLE h)
    (horizontalBottomToStageMap j) (Subsingleton.elim _ _)

/-- The linear complete-stage homology map, transported through the actual
bottom-relative comparisons. -/
def secondTranslationBKStageHomologyModuleMap (d : ℕ) {i j : EInt} (h : i ≤ j) :
    secondTranslationBKStageHomologyModule (C := C) R d i ⟶
      secondTranslationBKStageHomologyModule (C := C) R d j :=
  (secondTranslationBKStageModuleIso (C := C) R d i).inv ≫
    ((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap h) ≫
    (secondTranslationBKStageModuleIso (C := C) R d j).hom

@[simp]
theorem secondTranslationBKStageModuleIso_hom_apply (d : ℕ) (i : EInt)
    (x : secondTranslationBKStageIntervalModule (C := C) R d i) :
    (secondTranslationBKStageModuleIso (C := C) R d i).hom x =
      (horizontalBottomRelativeHomologyStageIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i d).hom
        ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
          (-(d : ℤ)) (secondTranslationBKStageInterval i)).asModuleEquiv x) := rfl

/-- The canonical underlying-group comparisons commute with every actual
module interval map. -/
theorem secondTranslationBKStageIntervalModuleMap_equiv (d : ℕ) {i j : EInt} (h : i ≤ j)
    (x : secondTranslationBKStageIntervalModule (C := C) R d i) :
    ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
      (-(d : ℤ)) (secondTranslationBKStageInterval j)).asModuleEquiv
      (((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).map
        (secondTranslationBKStageIntervalMap h) x)) =
    (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map (secondTranslationBKStageIntervalMap h)
      ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
        (-(d : ℤ)) (secondTranslationBKStageInterval i)).asModuleEquiv x) := by
  let ρ := secondTranslationBKSpectralAction (C := C) R
  let f : ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalAction ρ (-(d : ℤ)) (secondTranslationBKStageInterval i) ⟶
      ((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalAction ρ (-(d : ℤ)) (secondTranslationBKStageInterval j) :=
    { hom := (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map (secondTranslationBKStageIntervalMap h)
      comm := fun a => ((ρ a).asHom.hom (-(d : ℤ))).naturality
        (secondTranslationBKStageIntervalMap h) |>.symm }
  have hf := ConcreteCategory.congr_hom
    ((Action.monoidAlgebraModuleForgetIso (Multiplicative (Skeleton C))).hom.naturality f) x
  change (Action.monoidAlgebraModuleForgetIso (Multiplicative (Skeleton C))).hom.app _
      ((Action.monoidAlgebraModuleFunctor (Multiplicative (Skeleton C))).map f x) =
    f.hom ((Action.monoidAlgebraModuleForgetIso (Multiplicative (Skeleton C))).hom.app _ x)
      at hf
  rw [Action.monoidAlgebraModuleForgetIso_hom_apply,
    Action.monoidAlgebraModuleForgetIso_hom_apply] at hf
  dsimp only [Functor.comp_map, ConcreteCategory.comp_apply,
    SpectralObject.intervalRepresentation, SpectralObject.intervalAction,
    secondTranslationBKModuleSpectralObject,
    SpectralObject.monoidModule, SpectralObject.monoidModuleH,
    SpectralObject.monoidModuleMap, f, ρ, Action.forget] at hf ⊢
  exact hf

/-- This map's underlying function is the original complete-stage homology map. -/
theorem secondTranslationBKStageHomologyModuleMap_apply (d : ℕ) {i j : EInt} (h : i ≤ j)
    (x : secondTranslationBKStageHomologyModule (C := C) R d i) :
    secondTranslationBKStageHomologyModuleMap (C := C) R d h x =
      HomologicalComplex.homologyMap (horizontalCompleteFilteredTotalMap (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h) d x := by
  obtain ⟨y, rfl⟩ := (secondTranslationBKStageLinearEquiv (C := C) R d i).surjective x
  change secondTranslationBKStageHomologyModuleMap (C := C) R d h
      ((secondTranslationBKStageModuleIso (C := C) R d i).hom y) =
    HomologicalComplex.homologyMap (horizontalCompleteFilteredTotalMap (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h) d
      ((secondTranslationBKStageModuleIso (C := C) R d i).hom y)
  simp only [secondTranslationBKStageHomologyModuleMap, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply]
  rw [secondTranslationBKStageModuleIso_hom_apply,
    secondTranslationBKStageIntervalModuleMap_equiv,
    secondTranslationBKStageModuleIso_hom_apply]
  have hn := horizontalBottomRelativeHomologyStageIso_naturality (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h d
  simpa only [ConcreteCategory.comp_apply, secondTranslationBKStageIntervalMap] using
    ConcreteCategory.congr_hom hn
      ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
        (-(d : ℤ)) (secondTranslationBKStageInterval i)).asModuleEquiv y)

/-- The full bottom-to-top spectral interval has its canonical comparison
with the original signed-total homology group. -/
def secondTranslationBKTopRelativeToTotalIso (d : ℕ) :
    (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).obj (secondTranslationBKStageInterval ⊤) ≅
      (((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).total (ComplexShape.down ℕ)).homology d :=
  horizontalBottomRelativeHomologyStageIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) ⊤ d

/-- The actual homology map from any complete stage to top is the original
inclusion into the signed total complex. -/
theorem secondTranslationBKStageToTop_eq (i : EInt) :
    horizontalCompleteFilteredTotalMap (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (show i ≤ ⊤ from le_top) =
      horizontalCompleteFilteredTotalToTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i := by
  have h := horizontalCompleteFilteredTotalMap_toTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (show i ≤ ⊤ from le_top)
  simpa only [horizontalCompleteFilteredTotalToTotal_top, Category.comp_id] using h

/-- The actual finite upper interval maps to the top interval by the original
canonical total-homology comparison. -/
theorem secondTranslationBKFiniteToTop_comp_total (d : ℕ) :
    (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map
        (secondTranslationBKStageIntervalMap
          (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top)) ≫
      (secondTranslationBKTopRelativeToTotalIso (C := C) R d).hom =
    (secondTranslationBKBottomRelativeToTotalIso (C := C) R d).hom := by
  let i := horizontalAbutmentUpperIndex 0 d
  have h := horizontalBottomRelativeHomologyStageIso_naturality (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))
    (show i ≤ ⊤ from le_top) d
  rw [secondTranslationBKStageToTop_eq, ← horizontalCompleteHomologyToTotal_eq (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) d i] at h
  rw [secondTranslationBKBottomRelativeToTotalIso_hom]
  simpa only [Nat.zero_add, i, secondTranslationBKStageIntervalMap,
    secondTranslationBKTopRelativeToTotalIso,
    Iso.trans_hom, asIso_hom] using h

/-- The finite upper to full abutment map is an isomorphism on the actual
interval group, derived from the canonical comparisons. -/
theorem secondTranslationBKFiniteToTop_isIso (d : ℕ) :
    IsIso ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap
        (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top))) := by
  have hc : IsIso ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap
        (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top)) ≫
      (secondTranslationBKTopRelativeToTotalIso (C := C) R d).hom) := by
    rw [secondTranslationBKFiniteToTop_comp_total]
    infer_instance
  let _ := hc
  exact IsIso.of_isIso_comp_right
    ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap
        (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top)))
    (secondTranslationBKTopRelativeToTotalIso (C := C) R d).hom

/-- Reflect the derived finite-to-top isomorphism through the underlying-group
functor; this is an isomorphism of the constructed interval modules. -/
def secondTranslationBKFiniteToTopModuleIso (d : ℕ) :
    secondTranslationBKStageIntervalModule (C := C) R d (horizontalAbutmentUpperIndex 0 d) ≅
      secondTranslationBKStageIntervalModule (C := C) R d ⊤ := by
  let f := ((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).map
    (secondTranslationBKStageIntervalMap
      (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top))
  have hf : IsIso ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map f) := by
    change IsIso ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap
        (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top)))
    exact secondTranslationBKFiniteToTop_isIso R d
  let _ := hf
  have hIso : IsIso f := isIso_of_reflects_iso f (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
  let _ := hIso
  exact asIso f

/-- The actual bottom-to-top module abutment is linearly isomorphic to the
literal signed-total homology module, through the constructed finite comparison. -/
def secondTranslationBKAbutmentModuleIso (d : ℕ) :
    secondTranslationBKStageIntervalModule (C := C) R d ⊤ ≅
      secondTranslationBKTotalHomologyModule (C := C) R d :=
  (secondTranslationBKFiniteToTopModuleIso (C := C) R d).symm ≪≫
    (secondTranslationBKBottomRelativeToTotalLinearEquiv (C := C) R d).toModuleIso

/-- The module abutment comparison retains the actual canonical top-relative
map on the original group, rather than choosing another total-homology map. -/
theorem secondTranslationBKAbutmentModuleIso_hom_apply (d : ℕ)
    (x : secondTranslationBKStageIntervalModule (C := C) R d ⊤) :
    (secondTranslationBKAbutmentModuleIso (C := C) R d).hom x =
      (secondTranslationBKTopRelativeToTotalIso (C := C) R d).hom
        ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
          (-(d : ℤ)) (secondTranslationBKStageInterval ⊤)).asModuleEquiv x) := by
  let e := secondTranslationBKFiniteToTopModuleIso (C := C) R d
  let y := e.inv x
  have hy : e.hom y = x := Iso.inv_hom_id_apply e x
  rw [← hy]
  change secondTranslationBKBottomRelativeToTotalLinearEquiv (C := C) R d
      (e.inv (e.hom y)) = _
  rw [Iso.hom_inv_id_apply, secondTranslationBKBottomRelativeToTotalLinearEquiv_apply,
    secondTranslationBKBottomRelativeToTotalAddEquiv_apply]
  have he : e.hom =
      ((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).map
        (secondTranslationBKStageIntervalMap
          (show horizontalAbutmentUpperIndex 0 d ≤ ⊤ from le_top)) := rfl
  rw [he, secondTranslationBKStageIntervalModuleMap_equiv]
  have hc := ConcreteCategory.congr_hom (secondTranslationBKFiniteToTop_comp_total R d)
    ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
      (-(d : ℤ)) (secondTranslationBKStageInterval (horizontalAbutmentUpperIndex 0
        d))).asModuleEquiv y)
  exact hc.symm

/-- The actual linear map from the homology of any complete stage into the
literal signed-total homology module. -/
def secondTranslationBKStageToTotalModuleMap (d : ℕ) (i : EInt) :
    secondTranslationBKStageHomologyModule (C := C) R d i ⟶
      secondTranslationBKTotalHomologyModule (C := C) R d :=
  (secondTranslationBKStageModuleIso (C := C) R d i).inv ≫
    ((secondTranslationBKModuleSpectralObject (C := C) R).H (-(d : ℤ))).map
      (secondTranslationBKStageIntervalMap (show i ≤ ⊤ from le_top)) ≫
    (secondTranslationBKAbutmentModuleIso (C := C) R d).hom

/-- Every extended-stage-to-total module map is the original signed-total
inclusion on homology, including stages above the finite upper cut and top. -/
theorem secondTranslationBKStageToTotalModuleMap_apply (d : ℕ) (i : EInt)
    (x : secondTranslationBKStageHomologyModule (C := C) R d i) :
    secondTranslationBKStageToTotalModuleMap (C := C) R d i x =
      HomologicalComplex.homologyMap (horizontalCompleteFilteredTotalToTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i) d x := by
  obtain ⟨y, rfl⟩ := (secondTranslationBKStageLinearEquiv (C := C) R d i).surjective x
  change secondTranslationBKStageToTotalModuleMap (C := C) R d i
      ((secondTranslationBKStageModuleIso (C := C) R d i).hom y) =
    HomologicalComplex.homologyMap (horizontalCompleteFilteredTotalToTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) i) d
      ((secondTranslationBKStageModuleIso (C := C) R d i).hom y)
  simp only [secondTranslationBKStageToTotalModuleMap, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply]
  rw [secondTranslationBKAbutmentModuleIso_hom_apply,
    secondTranslationBKStageIntervalModuleMap_equiv,
    secondTranslationBKStageModuleIso_hom_apply]
  have hn := horizontalBottomRelativeHomologyStageIso_naturality (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (show i ≤ ⊤ from le_top) d
  rw [secondTranslationBKStageToTop_eq] at hn
  have hp := ConcreteCategory.congr_hom hn
    ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
      (-(d : ℤ)) (secondTranslationBKStageInterval i)).asModuleEquiv y)
  dsimp only [ConcreteCategory.comp_apply, secondTranslationBKStageIntervalMap,
    secondTranslationBKTopRelativeToTotalIso] at hp ⊢
  exact hp

/-- For every decomposition of the total degree, the original canonical
bottom-relative comparison lands linearly in the same literal total module. -/
def secondTranslationBKCanonicalToTotalModuleMap (p q : ℕ) :
    ((secondTranslationBKModuleSpectralObject (C := C) R).H
      (-((p + q : ℕ) : ℤ))).obj (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ⟶
      secondTranslationBKTotalHomologyModule (C := C) R (p + q) :=
  (secondTranslationBKStageModuleIso (C := C) R (p + q)
    (horizontalAbutmentUpperIndex p q)).hom ≫
      secondTranslationBKStageToTotalModuleMap (C := C) R (p + q)
        (horizontalAbutmentUpperIndex p q)

/-- The map for arbitrary `(p,q)` is exactly the original canonical
bottom-relative-to-total homology comparison, with no replacement map. -/
theorem secondTranslationBKCanonicalToTotalModuleMap_apply (p q : ℕ)
    (x : ((secondTranslationBKModuleSpectralObject (C := C) R).H
      (-((p + q : ℕ) : ℤ))).obj (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) :
    secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q x =
      (horizontalBottomRelativeHomologyToTotalIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) p q).hom
        ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalRepresentation (secondTranslationBKSpectralAction (C := C) R)
          (-((p + q : ℕ) : ℤ))
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q))).asModuleEquiv x) := by
  rw [secondTranslationBKCanonicalToTotalModuleMap, ConcreteCategory.comp_apply,
    secondTranslationBKStageToTotalModuleMap_apply, secondTranslationBKStageModuleIso_hom_apply]
  dsimp only [horizontalBottomRelativeHomologyToTotalIso,
    horizontalAbutmentUpperHomologyToTotalIso, Iso.trans_hom, asIso_hom]
  rw [horizontalCompleteHomologyToTotal_eq]
  rfl

/-- Every canonical degree decomposition uses the constructed scalar action
on the one literal total-homology module in degree `p+q`. -/
theorem secondTranslationBKCanonicalToTotalModuleMap_smul (p q : ℕ) (r : A)
    (x : ((secondTranslationBKModuleSpectralObject (C := C) R).H
      (-((p + q : ℕ) : ℤ))).obj (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) :
    secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q (r • x) =
      r • secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q x :=
  (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q).hom.map_smul r x

/-- The literal total module retains the original additive group exactly. -/
theorem secondTranslationBKTotalHomologyModule_forget (d : ℕ) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        (secondTranslationBKTotalHomologyModule (C := C) R d) =
      (((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).total (ComplexShape.down ℕ)).homology d := rfl

/-- Every canonical comparison is an isomorphism of the constructed modules,
derived from the original additive canonical isomorphism. -/
instance secondTranslationBKCanonicalToTotalModuleMap_isIso (p q : ℕ) :
    IsIso (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q) := by
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let e := (Action.monoidAlgebraModuleForgetIso (Multiplicative (Skeleton C))).app
    (((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).intervalAction (secondTranslationBKSpectralAction (C := C) R)
      (-((p + q : ℕ) : ℤ)) (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) ≪≫
      horizontalBottomRelativeHomologyToTotalIso (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) p q
  have hm : U.map (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q) =
      e.hom := by
    ext x
    change secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q x = e.hom x
    rw [secondTranslationBKCanonicalToTotalModuleMap_apply]
    simp only [e, Iso.trans_hom, ConcreteCategory.comp_apply,
      Iso.app_hom, Action.monoidAlgebraModuleForgetIso_hom_apply,
      SpectralObject.intervalRepresentation]
    rfl
  have hIso : IsIso (U.map
      (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q)) := by
    rw [hm]
    infer_instance
  let _ := hIso
  exact isIso_of_reflects_iso _ U

/-- The original canonical comparison for each decomposition of the degree,
as an isomorphism into the one fixed literal total-homology module. -/
def secondTranslationBKCanonicalToTotalModuleIso (p q : ℕ) :
    ((secondTranslationBKModuleSpectralObject (C := C) R).H
      (-((p + q : ℕ) : ℤ))).obj (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≅
      secondTranslationBKTotalHomologyModule (C := C) R (p + q) :=
  asIso (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q)

/-- Every degree decomposition has the same prescribed total generator
action through its original canonical comparison. -/
theorem secondTranslationBKCanonicalToTotalModuleMap_single_apply (p q : ℕ)
    (B : C) (z : ℤ)
    (x : ((secondTranslationBKModuleSpectralObject (C := C) R).H
      (-((p + q : ℕ) : ℤ))).obj (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) :
    secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton B)) z • x) =
      z • HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R B) (p + q)
        (secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q x) := by
  rw [(secondTranslationBKCanonicalToTotalModuleMap (C := C) R p q).hom.map_smul]
  exact secondTranslationBKTotalHomologyModule_single_apply R (p + q) B z _

/-- Actual complete-stage transition maps commute with their literal total
homology maps in the module category. -/
theorem secondTranslationBKStageModuleMap_comp_toTotal (d : ℕ) {i j : EInt} (h : i ≤ j) :
    secondTranslationBKStageHomologyModuleMap (C := C) R d h ≫
        secondTranslationBKStageToTotalModuleMap (C := C) R d j =
      secondTranslationBKStageToTotalModuleMap (C := C) R d i := by
  apply ModuleCat.hom_ext
  ext x
  simp only [ConcreteCategory.comp_apply, secondTranslationBKStageToTotalModuleMap_apply,
    secondTranslationBKStageHomologyModuleMap_apply]
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f => HomologicalComplex.homologyMap f d)
      (horizontalCompleteFilteredTotalMap_toTotal (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h)) x
  simpa only [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] using he

end CategoryTheory.SInverseS

end
