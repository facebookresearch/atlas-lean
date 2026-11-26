/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageStalks
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleSkyscraperSections
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Ring.Prod

/-!
# Nonzero skyscraper coefficients on a two-component affine scheme

Let `K` be the algebraic closure of `ℚ`. The diagonal `K → K×K` gives
`f : Spec(K×K) → Spec K`, and the two projections give distinct geometric
sections. Coefficients are `ULift.{1} ℤ`, in a universe above the schemes.

Constant terminal sections are built using the categorical product diagonal.
The actual inverse-image/common-stalk comparison's skyscraper mate evaluates
these sections to one and intertwines the nonidentity doubling coefficient
map. The actual geometric stalk counit evaluates the corresponding germ to
one and its doubled image to two. Global-section evaluation gives the same
nonzero coefficients. These are stalk, section and mate coordinates.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.DerivedSections Opposite

namespace MathlibExtTest.AlgebraicGeometry.Sites.SmallEtaleNonzero

private abbrev K := AlgebraicClosure ℚ

private abbrev Coeff := ULift.{1} ℤ

private abbrev A : AddCommGrpCat.{1} := AddCommGrpCat.of Coeff

private abbrev X : Scheme.{0} := Spec (.of K)

private abbrev Y : Scheme.{0} := Spec (.of (K × K))

private abbrev diagonal : K →+* K × K := (RingHom.id K).prod (RingHom.id K)

private abbrev f : Y ⟶ X := Spec.map (CommRingCat.ofHom diagonal)

private abbrev q : Spec (.of K) ⟶ Y := Spec.map (CommRingCat.ofHom (RingHom.fst K K))

private abbrev q' : Spec (.of K) ⟶ Y := Spec.map (CommRingCat.ofHom (RingHom.snd K K))

private abbrev P := smallEtaleGeometricPointCommon.{0, 1} q

private abbrev R := smallEtaleGeometricPointCommon.{0, 1} (q ≫ f)

private abbrev U : X.Etale := Scheme.Etale.mk (𝟙 X)

private abbrev V : Y.Etale := Scheme.Etale.mk (𝟙 Y)

private abbrev FX : Sheaf X.smallEtaleTopology AddCommGrpCat.{1} :=
  R.skyscraperSheafFunctor.obj A

private abbrev FY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{1} :=
  P.skyscraperSheafFunctor.obj A

private def double : Coeff →+ Coeff :=
  AddMonoidHom.id Coeff + AddMonoidHom.id Coeff

private abbrev μ : A ⟶ A := AddCommGrpCat.ofHom double

private abbrev τX : FX ⟶ FX := R.skyscraperSheafFunctor.map μ

private abbrev τY : FY ⟶ FY := P.skyscraperSheafFunctor.map μ

private def z : P.fiber.obj V := by
  letI : Unique (P.fiber.obj V) := P.uniqueFiberObj V (identityEtaleIsTerminal Y)
  exact default

private def zB : P.fiber.obj ((smallEtaleBaseChange f).obj U) :=
  P.fiber.map (smallEtaleBaseChangeTerminalIso f).inv z

private def zX : R.fiber.obj U :=
  (smallEtaleBaseChangeCommonPointFiberIso.{0, 1} f q).hom.app U zB

private def constantProduct {S : Scheme.{0}} (Φ : S.smallEtaleTopology.Point.{1})
    (W : S.Etale) (n : ℤ) : (Φ.skyscraperSheafFunctor.obj A).obj.obj (op W) :=
  (Pi.lift (fun _ : Φ.fiber.obj W => 𝟙 A)) (ULift.up n)

private lemma constantProduct_coordinate {S : Scheme.{0}}
    (Φ : S.smallEtaleTopology.Point.{1}) (W : S.Etale) (w : Φ.fiber.obj W) (n : ℤ) :
    Pi.π (fun _ : Φ.fiber.obj W => A) w (constantProduct Φ W n) = ULift.up n :=
  ConcreteCategory.congr_hom (Pi.lift_comp_π (fun _ : Φ.fiber.obj W => 𝟙 A) w) (ULift.up n)

private lemma skyscraper_map_coordinate {S : Scheme.{0}}
    (Φ : S.smallEtaleTopology.Point.{1}) (W : S.Etale) (w : Φ.fiber.obj W)
    (s : (Φ.skyscraperSheafFunctor.obj A).obj.obj (op W)) :
    Pi.π (fun _ : Φ.fiber.obj W => A) w
        (((Φ.skyscraperSheafFunctor.map μ).hom.app (op W)) s) =
      double (Pi.π (fun _ : Φ.fiber.obj W => A) w s) := by
  change Pi.π (fun _ : Φ.fiber.obj W => A) w
    ((Pi.map (fun _ : Φ.fiber.obj W => μ)) s) = μ (Pi.π _ w s)
  exact ConcreteCategory.congr_hom (Pi.map_π (fun _ : Φ.fiber.obj W => μ) w) s

private abbrev ρ : FX ⟶ (smallEtaleDirectImage.{0, 1} f).obj FY :=
  (smallEtaleInverseImageCommonGeometricStalkRightIso.{0, 1} f q).hom.app A

private abbrev σ : (smallEtaleDirectImage.{0, 1} f).obj FY ⟶
    (smallEtaleDirectImage.{0, 1} f).obj FY :=
  (smallEtaleDirectImage.{0, 1} f).map τY

private def mateCoordinate
    (s : ((smallEtaleDirectImage.{0, 1} f).obj FY).obj.obj (op U)) : Coeff :=
  Pi.π (fun _ : P.fiber.obj ((smallEtaleBaseChange f).obj U) => A) zB s

private lemma mate_coordinate (s : FX.obj.obj (op U)) :
    mateCoordinate (ρ.hom.app (op U) s) = Pi.π (fun _ : R.fiber.obj U => A) zX s :=
  ConcreteCategory.congr_hom
    (smallEtaleInverseImageCommonGeometricStalkRightIso_hom_app_π.{0, 1} f q A U zB) s

private lemma mate_constant (n : ℤ) :
    mateCoordinate (ρ.hom.app (op U) (constantProduct R U n)) = ULift.up n :=
  (mate_coordinate (constantProduct R U n)).trans (constantProduct_coordinate R U zX n)

private lemma mate_doubled (n : ℤ) :
    mateCoordinate (ρ.hom.app (op U) (τX.hom.app (op U) (constantProduct R U n))) =
      ULift.up (n + n) :=
  (mate_coordinate (τX.hom.app (op U) (constantProduct R U n))).trans
    ((skyscraper_map_coordinate R U zX (constantProduct R U n)).trans
      (congrArg double (constantProduct_coordinate R U zX n)))

private lemma mate_naturality (s : FX.obj.obj (op U)) :
    mateCoordinate (ρ.hom.app (op U) (τX.hom.app (op U) s)) =
      mateCoordinate (σ.hom.app (op U) (ρ.hom.app (op U) s)) := by
  have hn : τX ≫ ρ = ρ ≫ σ :=
    (smallEtaleInverseImageCommonGeometricStalkRightIso.{0, 1} f q).hom.naturality μ
  have hU : τX.hom.app (op U) ≫ ρ.hom.app (op U) =
      ρ.hom.app (op U) ≫ σ.hom.app (op U) :=
    congrArg (fun m : FX ⟶ (smallEtaleDirectImage.{0, 1} f).obj FY => m.hom.app (op U)) hn
  exact congrArg mateCoordinate (ConcreteCategory.congr_hom hU s)

private def germ (n : ℤ) : (P.sheafFiber (A := AddCommGrpCat.{1})).obj FY :=
  P.toPresheafFiber V z FY.obj (constantProduct P V n)

private abbrev ε : (P.sheafFiber (A := AddCommGrpCat.{1})).obj FY ⟶ A :=
  P.skyscraperSheafAdjunction.counit.app A

private lemma germ_coefficient (n : ℤ) : ε (germ n) = ULift.up n :=
  (ConcreteCategory.congr_hom
    (P.toPresheafFiber_skyscraperSheafAdjunction_counit A V z)
      (constantProduct P V n)).trans (constantProduct_coordinate P V z n)

private lemma doubled_germ_coefficient (n : ℤ) :
    ε ((P.sheafFiber (A := AddCommGrpCat.{1})).map τY (germ n)) = ULift.up (n + n) := by
  have h : (P.sheafFiber (A := AddCommGrpCat.{1})).map τY ≫ ε = ε ≫ μ :=
    P.skyscraperSheafAdjunction.counit.naturality μ
  exact (ConcreteCategory.congr_hom h (germ n)).trans (congrArg μ (germ_coefficient n))

private abbrev Γ := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{1}

private def globalSection (n : ℤ) : Γ.obj FY :=
  (smallEtaleGlobalTerminalIso.{0, 1} Y).inv.app FY (constantProduct P V n)

private abbrev globalCoordinate : Γ.obj FY ⟶ A :=
  (smallEtaleSkyscraperSectionsIso.{0, 1} q).hom.app A

private lemma global_coefficient (n : ℤ) : globalCoordinate (globalSection n) = ULift.up n := by
  have h : (smallEtaleGlobalTerminalIso.{0, 1} Y).hom.app FY (globalSection n) =
      constantProduct P V n :=
    ConcreteCategory.congr_hom ((smallEtaleGlobalTerminalIso.{0, 1} Y).app FY).inv_hom_id
      (constantProduct P V n)
  exact (smallEtaleSkyscraperSectionsIso_hom_apply.{0, 1} q A z (globalSection n)).trans
    ((congrArg (fun s => Pi.π (fun _ : P.fiber.obj V => A) z s) h).trans
      (constantProduct_coordinate P V z n))

example : q ≠ q' := by
  intro hq
  have hr := Spec.map_injective hq
  have hx := congrArg (fun e : CommRingCat.of (K × K) ⟶ CommRingCat.of K =>
    e.hom (1, 0)) hr
  change (1 : K) = 0 at hx
  exact one_ne_zero hx

example : (RingHom.fst K K).comp diagonal = RingHom.id K ∧
    (RingHom.snd K K).comp diagonal = RingHom.id K := ⟨by ext x; rfl, by ext x; rfl⟩

example : μ (ULift.up (1 : ℤ)) = (ULift.up (2 : ℤ) : Coeff) := rfl

example : mateCoordinate (ρ.hom.app (op U) (constantProduct R U 1)) =
    ULift.up (1 : ℤ) := mate_constant 1

example : mateCoordinate (ρ.hom.app (op U) (τX.hom.app (op U) (constantProduct R U 1))) =
    ULift.up (2 : ℤ) := mate_doubled 1

example : mateCoordinate (σ.hom.app (op U) (ρ.hom.app (op U) (constantProduct R U 1))) =
    ULift.up (2 : ℤ) :=
  (mate_naturality (constantProduct R U 1)).symm.trans (mate_doubled 1)

example : τX ≠ 𝟙 FX := by
  intro ht
  have hx := congrArg (fun t : FX ⟶ FX =>
    Pi.π (fun _ : R.fiber.obj U => A) zX (t.hom.app (op U) (constantProduct R U 1))) ht
  have hl : Pi.π (fun _ : R.fiber.obj U => A) zX
      (τX.hom.app (op U) (constantProduct R U 1)) = ULift.up (2 : ℤ) :=
    (skyscraper_map_coordinate R U zX (constantProduct R U 1)).trans
      (congrArg double (constantProduct_coordinate R U zX 1))
  have hr : Pi.π (fun _ : R.fiber.obj U => A) zX
      ((𝟙 FX).hom.app (op U) (constantProduct R U 1)) = ULift.up (1 : ℤ) :=
    constantProduct_coordinate R U zX 1
  exact (by decide : (2 : ℤ) ≠ 1) (congrArg ULift.down (hl.symm.trans (hx.trans hr)))

example : ε (germ 1) = ULift.up (1 : ℤ) := germ_coefficient 1

example : germ 1 ≠ 0 := by
  intro hg
  have hx := congrArg ε hg
  rw [germ_coefficient, map_zero] at hx
  exact (by decide : (ULift.up (1 : ℤ) : Coeff) ≠ 0) hx

example : ε ((P.sheafFiber (A := AddCommGrpCat.{1})).map τY (germ 1)) =
    ULift.up (2 : ℤ) := doubled_germ_coefficient 1

example : (P.sheafFiber (A := AddCommGrpCat.{1})).map τY (germ 1) ≠ germ 1 := by
  intro heq
  have hx := congrArg ε heq
  rw [doubled_germ_coefficient, germ_coefficient] at hx
  exact (by decide : (2 : ℤ) ≠ 1) (congrArg ULift.down hx)

example : globalCoordinate (globalSection 1) = ULift.up (1 : ℤ) := global_coefficient 1

example : globalCoordinate (Γ.map τY (globalSection 1)) = ULift.up (2 : ℤ) :=
  (smallEtaleSkyscraperSectionsIso_naturality.{0, 1} q μ (globalSection 1)).trans
    (congrArg μ (global_coefficient 1))

example : Γ.map τY (globalSection 1) ≠ 0 := by
  intro heq
  have hx := congrArg globalCoordinate heq
  have hv : globalCoordinate (Γ.map τY (globalSection 1)) = ULift.up (2 : ℤ) :=
    (smallEtaleSkyscraperSectionsIso_naturality.{0, 1} q μ (globalSection 1)).trans
      (congrArg μ (global_coefficient 1))
  rw [hv, map_zero] at hx
  exact (by decide : (ULift.up (2 : ℤ) : Coeff) ≠ 0) hx

end MathlibExtTest.AlgebraicGeometry.Sites.SmallEtaleNonzero
