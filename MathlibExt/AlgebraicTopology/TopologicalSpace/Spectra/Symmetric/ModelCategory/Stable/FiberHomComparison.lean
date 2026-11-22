/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.ChosenCofiberExactness

/-!
# Original symmetric fiber comparisons on every shifted Hom test

The actual original suspended-fiber comparison induces a function from
every original Q-cofiber Hom set to the next integer fiber Hom set. Its
source is the caller's unchanged limit point and its source action is the
entire chosen-fiber map of each original Arrow square. The inverse scalar
adjunct, original Q counit, native delta and original suspension comparison
are the functions already used in `ShiftedHom`.

Both arbitrary limit choices and arbitrary Q-cofiber colimit choices are
retained in the complete comparison functions. The original comparison is
constructed before its stable equivalence is proved. No bijectivity or
model-structure dictionary is supplied to these functions.

This is the Hom comparison used in MMSS, *Model categories of diagram
spectra*, December 30, 1999 manuscript, Theorems 7.4(vi) and 8.12(vi).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev Index := PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ISusp := OriginalISuspension.suspension (B := B) (I := Index)
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := Index)
private abbrev KRight := NativeK.OriginalFiberComparison.rightArrowProperty
  Actual.symmetricFamily.{u, v}
private abbrev FiberChoices :=
  ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right)
private abbrev CofiberChoices :=
  ∀ F : Arrow C.{u, v}, PushoutCocone
    ((OriginalICone.inclusion (B := B) (I := Index)).app F.left) F.hom

private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

/-- The complete original comparison induces the degree-changing fiber Hom function. -/
def cofiberToFiberHom
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) q (CQ.obj F.obj) E →
      ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E :=
  fun g => ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE
    ((NativeK.OriginalFiberComparison.originalComparison (B := B)
      a ha Actual.symmetricFamily).app F ≫ g)

/-- The forward function retains the same original suspended-fiber comparison component. -/
theorem cofiberToFiberHom_apply
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) q (CQ.obj F.obj) E) :
    cofiberToFiberHom (B := B) a ha q F E hE g =
      ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE
        ((NativeK.OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F ≫ g) := rfl

/-- The whole inverse shift recovers the actual original comparison precomposition. -/
theorem cofiberToFiberHom_inverseShift
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) q (CQ.obj F.obj) E) :
    (ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE).symm
        (cofiberToFiberHom (B := B) a ha q F E hE g) =
      (NativeK.OriginalFiberComparison.originalComparison (B := B)
        a ha Actual.symmetricFamily).app F ≫ g :=
  (ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE).symm_apply_apply _

/-- Degree minus one uses the same actual negative Hom function supplied by native delta. -/
theorem cofiberToFiberHom_neg_one
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (-1) (CQ.obj F.obj) E) :
    cofiberToFiberHom (B := B) a ha (-1) F E hE g =
      NativeOmegaRecovery.NativeSymmetricDelooping.negativeHomEquiv (B := B)
        (a F.obj).pt E hE
        ((NativeK.OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F ≫ g) := by
  rw [cofiberToFiberHom_apply, ShiftedHom.suspensionHomEquiv_neg_one]
  rfl

/-- Every original cofiber null class maps to the same actual shifted fiber null class. -/
theorem cofiberToFiberHom_null
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    cofiberToFiberHom (B := B) a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E) := by
  have hNull :
      (NativeK.OriginalFiberComparison.originalComparison (B := B)
        a ha Actual.symmetricFamily).app F ≫
          OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((ShiftedTargets.target q).obj E) =
      OrdinaryHoCofiberKernel.nullHom (ISusp.obj (Q.obj (a F.obj).pt))
        ((ShiftedTargets.target q).obj E) :=
    ShiftedHom.nullHom_precomp (B := B)
      (show H.{u, v}.obj (ISusp.obj (Q.obj (a F.obj).pt)) ⟶ H.{u, v}.obj (CQ.obj F.obj) from
        (NativeK.OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F)
  exact (congrArg (ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE) hNull).trans
    (ShiftedHom.suspensionHomEquiv_null (B := B) q (a F.obj).pt E hE)

/-- Every entire original K-right Arrow square acts through the same chosen-fiber map. -/
theorem cofiberToFiberHom_source
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) {F G : KRight.{u, v}.FullSubcategory} (φ : F ⟶ G)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (CQ.obj G.obj) E) :
    cofiberToFiberHom (B := B) a ha q F E hE (H.{u, v}.map (CQ.map φ.hom) ≫ g) =
      H.{u, v}.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
        (a F.obj) (a G.obj) (ha G.obj)) ≫ cofiberToFiberHom (B := B) a ha q G E hE g := by
  have hNat :
      H.{u, v}.map (ISusp.map (Q.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
        (a F.obj) (a G.obj) (ha G.obj)))) ≫
          (NativeK.OriginalFiberComparison.originalComparison (B := B)
            a ha Actual.symmetricFamily).app G =
      (NativeK.OriginalFiberComparison.originalComparison (B := B)
        a ha Actual.symmetricFamily).app F ≫ H.{u, v}.map (CQ.map φ.hom) :=
    NativeK.OriginalFiberComparison.originalComparison_naturality (B := B)
      a ha Actual.symmetricFamily φ
  rw [cofiberToFiberHom_apply, cofiberToFiberHom_apply, ← Category.assoc,
    ← hNat, Category.assoc, ShiftedHom.suspensionHomEquiv_source]

/-- Every full actual Omega target transformation retains the whole fiber Hom function. -/
theorem cofiberToFiberHom_target
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) q (CQ.obj F.obj) E) :
    cofiberToFiberHom (B := B) a ha q F E' hE'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      cofiberToFiberHom (B := B) a ha q F E hE g ≫
        H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t) := by
  rw [cofiberToFiberHom_apply, cofiberToFiberHom_apply, ← Category.assoc]
  exact ShiftedHom.suspensionHomEquiv_target (B := B) q (a F.obj).pt hE hE' t _

/-- Both arbitrary original limit choices act on the same complete comparison function. -/
theorem cofiberToFiberHom_choice
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) q (CQ.obj F.obj) E) :
    H.{u, v}.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫
        cofiberToFiberHom (B := B) b hb q F E hE g =
      cofiberToFiberHom (B := B) a ha q F E hE g := by
  let γ := (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
    Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom
  have hChoice : H.{u, v}.map (ISusp.map (Q.map γ)) ≫
      (NativeK.OriginalFiberComparison.originalComparison (B := B)
        b hb Actual.symmetricFamily).app F =
    (NativeK.OriginalFiberComparison.originalComparison (B := B)
      a ha Actual.symmetricFamily).app F :=
    NativeK.OriginalFiberComparison.originalComparison_choice (B := B)
      a ha b hb Actual.symmetricFamily F
  change H.{u, v}.map γ ≫ _ = _
  rw [cofiberToFiberHom_apply, cofiberToFiberHom_apply,
    ← ShiftedHom.suspensionHomEquiv_source (B := B) q γ E hE,
    ← Category.assoc, hChoice]

/-- The inverse actual limit choice retains the whole original comparison function. -/
theorem cofiberToFiberHom_choice_inv
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : ShiftedHom.test (B := B) q (CQ.obj F.obj) E) :
    H.{u, v}.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv ≫
        cofiberToFiberHom (B := B) a ha q F E hE g =
      cofiberToFiberHom (B := B) b hb q F E hE g := by
  let e := H.{u, v}.mapIso (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
    Diagrams.zeroDiagram_isZero a ha b hb F.obj)
  apply (cancel_epi e.hom).mp
  change e.hom ≫ (e.inv ≫ cofiberToFiberHom (B := B) a ha q F E hE g) =
    e.hom ≫ cofiberToFiberHom (B := B) b hb q F E hE g
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (cofiberToFiberHom_choice (B := B) a ha b hb q F E hE g).symm

/-- The entire caller-chosen cofiber Hom comparison maps to its actual chosen fiber. -/
def chosenCofiberToFiberHom
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) q ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E →
      ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E :=
  fun g => cofiberToFiberHom (B := B) a ha q F E hE
    (ChosenCofiberTests.testHomEquiv (B := B) d hd q F.obj E g)

/-- The full chosen-cofiber function keeps the same original comparison and caller cofiber map. -/
theorem chosenCofiberToFiberHom_apply
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q
      ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E) :
    chosenCofiberToFiberHom (B := B) a ha d hd q F E hE g =
      ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE
        ((NativeK.OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F ≫
          H.{u, v}.map ((ChosenCofiberTests.choiceNatIso (B := B) d hd).hom.app F.obj) ≫ g) := by
  unfold chosenCofiberToFiberHom
  rw [ChosenCofiberTests.testHomEquiv_apply, cofiberToFiberHom_apply]

/-- Every actual caller cofiber null class maps to the original shifted chosen-fiber null class. -/
theorem chosenCofiberToFiberHom_null
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    chosenCofiberToFiberHom (B := B) a ha d hd q F E hE
        (OrdinaryHoCofiberKernel.nullHom
          ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj)
          ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E) := by
  unfold chosenCofiberToFiberHom
  rw [ChosenCofiberTests.testHomEquiv_null, cofiberToFiberHom_null]

/-- Every whole original Arrow square retains the caller cofiber and chosen-fiber source actions. -/
theorem chosenCofiberToFiberHom_source
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) {F G : KRight.{u, v}.FullSubcategory} (φ : F ⟶ G)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q
      ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj G.obj) E) :
    chosenCofiberToFiberHom (B := B) a ha d hd q F E hE
        (H.{u, v}.map ((ChosenCofiberTests.chosenCofiber (B := B) d hd).map φ.hom) ≫ g) =
      H.{u, v}.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
        (a F.obj) (a G.obj) (ha G.obj)) ≫
          chosenCofiberToFiberHom (B := B) a ha d hd q G E hE g := by
  unfold chosenCofiberToFiberHom
  rw [ChosenCofiberTests.testHomEquiv_source, cofiberToFiberHom_source]

/-- Every Omega target map acts on the entire original caller cofiber-to-fiber comparison. -/
theorem chosenCofiberToFiberHom_target
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : ShiftedHom.test (B := B) q
      ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E) :
    chosenCofiberToFiberHom (B := B) a ha d hd q F E' hE'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      chosenCofiberToFiberHom (B := B) a ha d hd q F E hE g ≫
        H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t) := by
  unfold chosenCofiberToFiberHom
  rw [ChosenCofiberTests.testHomEquiv_target,
    cofiberToFiberHom_target (B := B) a ha q F hE hE' t]

/-- Both entire limit choices retain the caller cofiber and original comparison functions. -/
theorem chosenCofiberToFiberHom_choice
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))
    (d : CofiberChoices (B := B)) (hd : ∀ F, IsColimit (d F))
    (q : ℤ) (F : KRight.{u, v}.FullSubcategory) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q
      ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E) :
    H.{u, v}.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫
        chosenCofiberToFiberHom (B := B) b hb d hd q F E hE g =
      chosenCofiberToFiberHom (B := B) a ha d hd q F E hE g := by
  unfold chosenCofiberToFiberHom
  exact cofiberToFiberHom_choice (B := B) a ha b hb q F E hE _

end PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison
