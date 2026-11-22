/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberIntegerConnecting
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberExactness

/-!
# The original chosen fiber sequence in every integer homotopy degree

The canonical positive tail at q is used to construct the original
connecting map from degree q+1. Both comparison functions and every
canonical integer cast are retained, including negative integers.
The original projection, map and connecting homomorphism are exact
at all three original integer groups.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo)
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r))

/-- The canonical target is the same original integer group under the actual degree equality. -/
def targetDegreeIso (q : ℤ) :
    integerStablePiFunctor.{u, v}
      (integerDegree (integerTailLevel q) (integerTailPositiveIndex q)) ≅
    integerStablePiFunctor q :=
  eqToIso (congrArg integerStablePiFunctor (integerDegree_canonical q))

/-- The canonical source is the same original successor-degree integer group. -/
def sourceDegreeIso (q : ℤ) :
    integerStablePiFunctor.{u, v}
      (integerDegree (integerTailLevel q) (integerTailPositiveIndex q) + 1) ≅
    integerStablePiFunctor (q + 1) :=
  eqToIso (congrArg integerStablePiFunctor (congrArg (fun d : ℤ => d + 1)
    (integerDegree_canonical q)))

/-- Every original integer fiber sequence has its actual connecting homomorphism. -/
def connectingPlusOne (q : ℤ) :
    (integerStablePiFunctor (q + 1)).obj Y ⟶ (integerStablePiFunctor q).obj c.pt :=
  (sourceDegreeIso q).inv.app Y ≫
    normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q) ≫
      (targetDegreeIso q).hom.app c.pt

/-- The full canonical integer connecting map retains the same normalized quotient function. -/
theorem connectingPlusOne_reconstruction (q : ℤ) :
    normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q) ≫
        (targetDegreeIso q).hom.app c.pt =
      (sourceDegreeIso q).hom.app Y ≫ connectingPlusOne p c hc hp q := by
  rw [connectingPlusOne, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Every integer group is exact at the original chosen fiber with its actual projection. -/
theorem exact_at_fiber (q : ℤ) :
    Function.MulExact (connectingPlusOne p c hc hp q).hom
      ((integerStablePiFunctor q).map c.fst).hom := by
  apply GrpCat.mulExact_of_iso_ladder
    ((sourceDegreeIso q).app Y).symm
    ((targetDegreeIso q).app c.pt).symm
    ((targetDegreeIso q).app X).symm
    (connectingPlusOne p c hc hp q) ((integerStablePiFunctor q).map c.fst)
    (normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q))
    ((integerStablePiFunctor
      (integerDegree (integerTailLevel q) (integerTailPositiveIndex q))).map c.fst)
  · let a := (sourceDegreeIso q).inv.app Y
    let d := normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)
    let e := (targetDegreeIso q).app c.pt
    change (a ≫ d ≫ e.hom) ≫ e.inv = a ≫ d
    calc
      _ = a ≫ ((d ≫ e.hom) ≫ e.inv) := Category.assoc a (d ≫ e.hom) e.inv
      _ = a ≫ (d ≫ (e.hom ≫ e.inv)) :=
        congrArg (fun z => a ≫ z) (Category.assoc d e.hom e.inv)
      _ = a ≫ (d ≫ 𝟙 _) := congrArg (fun z => a ≫ (d ≫ z)) e.hom_inv_id
      _ = a ≫ d := congrArg (fun z => a ≫ z) (Category.comp_id d)
  · exact (targetDegreeIso q).inv.naturality c.fst
  · exact normalized_exact_at_fiber p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)

/-- Every successor integer base group is exact with the original spectrum map. -/
theorem exact_at_base (q : ℤ) :
    Function.MulExact ((integerStablePiFunctor (q + 1)).map p).hom
      (connectingPlusOne p c hc hp q).hom := by
  apply GrpCat.mulExact_of_iso_ladder
    ((sourceDegreeIso q).app X).symm
    ((sourceDegreeIso q).app Y).symm
    ((targetDegreeIso q).app c.pt).symm
    ((integerStablePiFunctor (q + 1)).map p) (connectingPlusOne p c hc hp q)
    ((integerStablePiFunctor
      (integerDegree (integerTailLevel q) (integerTailPositiveIndex q) + 1)).map p)
    (normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q))
  · exact (sourceDegreeIso q).inv.naturality p
  · let a := (sourceDegreeIso q).inv.app Y
    let d := normalizedConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)
    let e := (targetDegreeIso q).app c.pt
    change (a ≫ d ≫ e.hom) ≫ e.inv = a ≫ d
    calc
      _ = a ≫ ((d ≫ e.hom) ≫ e.inv) := Category.assoc a (d ≫ e.hom) e.inv
      _ = a ≫ (d ≫ (e.hom ≫ e.inv)) :=
        congrArg (fun z => a ≫ z) (Category.assoc d e.hom e.inv)
      _ = a ≫ (d ≫ 𝟙 _) := congrArg (fun z => a ≫ (d ≫ z)) e.hom_inv_id
      _ = a ≫ d := congrArg (fun z => a ≫ z) (Category.comp_id d)
  · exact normalized_exact_at_base p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)

include hc hp in
/-- The same original integer maps are exact at the unchanged total spectrum. -/
theorem exact_at_total (q : ℤ) :
    Function.MulExact ((integerStablePiFunctor q).map c.fst).hom
      ((integerStablePiFunctor q).map p).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.integerStablePi_chosenFiber_exact_at_total
    p c hc hp q

/-- All three exact pairs use the same original integer groups and homomorphisms. -/
theorem three_exact_pairs (q : ℤ) :
    Function.MulExact ((integerStablePiFunctor q).map c.fst).hom
        ((integerStablePiFunctor q).map p).hom ∧
      Function.MulExact (connectingPlusOne p c hc hp q).hom
        ((integerStablePiFunctor q).map c.fst).hom ∧
      Function.MulExact ((integerStablePiFunctor (q + 1)).map p).hom
        (connectingPlusOne p c hc hp q).hom :=
  ⟨exact_at_total p c hc hp q, exact_at_fiber p c hc hp q, exact_at_base p c hc hp q⟩

/-- The same actual connecting map is indexed from q to the original degree q-1. -/
def connecting (q : ℤ) :
    (integerStablePiFunctor q).obj Y ⟶ (integerStablePiFunctor (q - 1)).obj c.pt :=
  (eqToIso (congrArg integerStablePiFunctor (show (q - 1) + 1 = q by omega))).inv.app Y ≫
    connectingPlusOne p c hc hp (q - 1)

/-- The actual integer degree cast reconstructs the same original connecting function. -/
theorem connecting_degree_cast (q : ℤ) :
    (eqToIso (congrArg integerStablePiFunctor (show (q - 1) + 1 = q by omega))).hom.app Y ≫
        connecting p c hc hp q = connectingPlusOne p c hc hp (q - 1) := by
  rw [connecting, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Exactness at the degree-q base retains the original map and actual q-to-q-1 connection. -/
theorem exact_at_base_degree (q : ℤ) :
    Function.MulExact ((integerStablePiFunctor q).map p).hom
      (connecting p c hc hp q).hom := by
  let e : integerStablePiFunctor ((q - 1) + 1) ≅ integerStablePiFunctor q :=
    eqToIso (congrArg integerStablePiFunctor (show (q - 1) + 1 = q by omega))
  apply GrpCat.mulExact_of_iso_ladder
    (e.app X).symm (e.app Y).symm (Iso.refl _)
    ((integerStablePiFunctor q).map p) (connecting p c hc hp q)
    ((integerStablePiFunctor ((q - 1) + 1)).map p)
    (connectingPlusOne p c hc hp (q - 1))
  · exact e.inv.naturality p
  · exact Category.comp_id _
  · exact exact_at_base p c hc hp (q - 1)

end PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence
