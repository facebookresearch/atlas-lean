/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindow
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTruncationAt
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingle
public import MathlibExt.Algebra.Homology.HomotopyCofiberMapCoordinates
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Signed identity disks in ambient-acyclic support windows

Let E be preadditive with zero and binary biproducts. The homotopy cofiber of identity on the
single complex in degree j has terms X in degrees j−1 and j and zero terms elsewhere. Under its
shifted-left and right term charts, the differential is positive identity. The identity-square
maps define an additive disk functor preserving every existing source pushout, and the identity
cofiber is contractible.

For an additive functor F:E→A to an abelian category, the image of this contraction makes every
disk F-acyclic. If a≤j−1 and j≤b, the disk lifts to the F-acyclic [a,b] window. With E exact and
F exact, admissible monos give componentwise cofibrations and the supported disk functor is
Waldhausen exact.

Source and ambient object and Hom universes remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded.SignedDisk

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Sending X to
the identity arrow of its single complex, and each E-map to the induced commuting identity
square, defines a functor E→Arrow(CochainComplex(E,ℤ)). -/
private abbrev singleArrow (j : ℤ) : E ⥤ Arrow (CochainComplex E ℤ) :=
  NatTrans.arrow (𝟙 (HomologicalComplex.single E (.up ℤ) j))

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The
identity-square maps of single complexes induce a functor X↦Dʲ(X) from E to integer cochains. -/
abbrev raw (j : ℤ) : E ⥤ CochainComplex E ℤ :=
  { NatTrans.arrow (𝟙 (HomologicalComplex.single E (.up ℤ) j)) ⋙
      HomologicalComplex.homotopyCofiberFunctor
      (fun k => ⟨k - 1, by change k - 1 + 1 = k; omega⟩) with
    obj := fun X => HomologicalComplex.homotopyCofiber
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) }

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Its value at X
is the homotopy cofiber of id on the single complex in degree j. -/
theorem raw_obj (j : ℤ) (X : E) :
    (raw E j).obj X = HomologicalComplex.homotopyCofiber
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For f:X→Y, the
map Dʲ(f) is the homotopy-cofiber map of the commuting identity square whose two legs are the
single-complex map of f. -/
theorem raw_map (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    (raw E j).map f = HomologicalComplex.homotopyCofiber.mapArrowHom
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X))
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj Y))
      (fun k => ⟨k - 1, by change k - 1 + 1 = k; omega⟩)
      ((NatTrans.arrow (𝟙 (HomologicalComplex.single E (.up ℤ) j))).map f) := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For any bounded
K, Dʲ(Kʲ) is the top-disk raw complex constructed from its degree-j term. -/
theorem raw_obj_topDisk (j : ℤ) (K : Bounded E) :
    (raw E j).obj (K.obj.X j) = TruncationAt.topDiskRaw (b := j) K := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The term Dʲ(X)ᵖ
is zero whenever p≠j−1 and p≠j. -/
theorem isZero_X (j : ℤ) (X : E) (p : ℤ) (hLower : p ≠ j - 1) (hUpper : p ≠ j) :
    IsZero (((raw E j).obj X).X p) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) p
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) j X p hUpper
  · intro q hpq
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) j X q
      (by change p + 1 = q at hpq; omega)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The shifted
left summand gives the lower chart X≅Dʲ(X)ʲ⁻¹. -/
def lowerIso (j : ℤ) (X : E) : X ≅ ((raw E j).obj X).X (j - 1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) j X).symm ≪≫
    isoBiprodZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) j X (j - 1) (by omega)) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) (j - 1) j
      (ComplexShape.up_mk _ _ (by omega))).symm

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The right
summand gives the upper chart X≅Dʲ(X)ʲ. -/
def upperIso (j : ℤ) (X : E) : X ≅ ((raw E j).obj X).X j :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) j X).symm ≪≫
    isoZeroBiprod (HomologicalComplex.isZero_single_obj_X (.up ℤ) j X (j + 1) (by omega)) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j + 1)
      (ComplexShape.up_mk _ _ rfl)).symm

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. On X=Kʲ for a
bounded complex K, this lower chart is the lower chart of its top-term disk. -/
theorem lowerIso_topTerm (j : ℤ) (K : Bounded E) :
    lowerIso E j (K.obj.X j) = TruncationAt.topDiskLowerIso (b := j) K := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. On X=Kʲ for a
bounded complex K, this upper chart is the upper chart of its top-term disk. -/
theorem upperIso_topTerm (j : ℤ) (K : Bounded E) :
    upperIso E j (K.obj.X j) = TruncationAt.topDiskUpperIso (b := j) K := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The forward
lower chart is the single-term identification followed by the cofiber's shifted left inclusion. -/
theorem lowerIso_hom (j : ℤ) (X : E) :
    (lowerIso E j X).hom = (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫
      HomologicalComplex.homotopyCofiber.inlX
        (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
        (ComplexShape.up_mk _ _ (by omega)) := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The forward
upper chart is the single-term identification followed by the cofiber's right inclusion. -/
theorem upperIso_hom (j : ℤ) (X : E) :
    (upperIso E j X).hom = (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫
      HomologicalComplex.homotopyCofiber.inrX
        (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j := by
  exact congrArg (fun f => (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫ f)
    (HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) (j + 1) j
      (ComplexShape.up_mk _ _ rfl))

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The lower chart
followed by dʲ⁻¹ equals the upper chart, so the differential is positive identity in these
coordinates. -/
theorem lowerIso_hom_d (j : ℤ) (X : E) :
    (lowerIso E j X).hom ≫ ((raw E j).obj X).d (j - 1) j = (upperIso E j X).hom := by
  have hd := HomologicalComplex.homotopyCofiber.inlX_d
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) (j - 1) j (j + 1)
    (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)
  have hpos : HomologicalComplex.homotopyCofiber.inlX
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
      (ComplexShape.up_mk _ _ (by omega)) ≫ ((raw E j).obj X).d (j - 1) j =
      HomologicalComplex.homotopyCofiber.inrX
        (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j := by
    change HomologicalComplex.homotopyCofiber.inlX
      (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
      (ComplexShape.up_mk _ _ (by omega)) ≫ HomologicalComplex.homotopyCofiber.d
        (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) (j - 1) j = _
    simpa only [HomologicalComplex.single_obj_d, neg_zero, zero_comp,
      HomologicalComplex.id_f, Category.id_comp, zero_add] using hd
  calc
    _ = ((HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫
        HomologicalComplex.homotopyCofiber.inlX
          (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
          (ComplexShape.up_mk _ _ (by omega))) ≫ ((raw E j).obj X).d (j - 1) j :=
      congrArg (fun f => f ≫ ((raw E j).obj X).d (j - 1) j) (lowerIso_hom E j X)
    _ = (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫
        (HomologicalComplex.homotopyCofiber.inlX
          (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
          (ComplexShape.up_mk _ _ (by omega)) ≫ ((raw E j).obj X).d (j - 1) j) :=
      Category.assoc _ _ _
    _ = (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫
        HomologicalComplex.homotopyCofiber.inrX
          (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j :=
      congrArg (fun f => (HomologicalComplex.singleObjXSelf (.up ℤ) j X).inv ≫ f) hpos
    _ = _ := (upperIso_hom E j X).symm

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Conjugating
dʲ⁻¹ by the lower and upper charts gives id_X. -/
theorem lowerIso_hom_d_upperIso_inv (j : ℤ) (X : E) :
    (lowerIso E j X).hom ≫ ((raw E j).obj X).d (j - 1) j ≫ (upperIso E j X).inv = 𝟙 X := by
  rw [← Category.assoc, lowerIso_hom_d, Iso.hom_inv_id]

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For f:X→Y, the
lower chart of X followed by Dʲ(f)ʲ⁻¹ equals f followed by the lower chart of Y. -/
theorem lowerIso_naturality (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    (lowerIso E j X).hom ≫ ((raw E j).map f).f (j - 1) = f ≫ (lowerIso E j Y).hom := by
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) j X
  let sY := HomologicalComplex.singleObjXSelf (.up ℤ) j Y
  let u := HomologicalComplex.homotopyCofiber.inlX
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j (j - 1)
    (ComplexShape.up_mk _ _ (by omega))
  let v := HomologicalComplex.homotopyCofiber.inlX
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj Y)) j (j - 1)
    (ComplexShape.up_mk _ _ (by omega))
  have hs : sX.inv ≫ ((HomologicalComplex.single E (.up ℤ) j).map f).f j = f ≫ sY.inv :=
    ((HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).inv.naturality f).symm
  have hm : u ≫ ((raw E j).map f).f (j - 1) =
      ((HomologicalComplex.single E (.up ℤ) j).map f).f j ≫ v :=
    HomologicalComplex.homotopyCofiber.inlX_mapArrowHom
      (fun k => ⟨k - 1, by change k - 1 + 1 = k; omega⟩)
      ((singleArrow E j).map f) j (j - 1) (ComplexShape.up_mk _ _ (by omega))
  calc
    _ = (sX.inv ≫ u) ≫ ((raw E j).map f).f (j - 1) :=
      congrArg (fun g => g ≫ ((raw E j).map f).f (j - 1)) (lowerIso_hom E j X)
    _ = sX.inv ≫ (u ≫ ((raw E j).map f).f (j - 1)) := Category.assoc _ _ _
    _ = sX.inv ≫ (((HomologicalComplex.single E (.up ℤ) j).map f).f j ≫ v) :=
      congrArg (fun g => sX.inv ≫ g) hm
    _ = (sX.inv ≫ ((HomologicalComplex.single E (.up ℤ) j).map f).f j) ≫ v :=
      (Category.assoc _ _ _).symm
    _ = (f ≫ sY.inv) ≫ v := congrArg (fun g => g ≫ v) hs
    _ = f ≫ (sY.inv ≫ v) := Category.assoc _ _ _
    _ = _ := congrArg (fun g => f ≫ g) (lowerIso_hom E j Y).symm

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For f:X→Y, the
upper chart of X followed by Dʲ(f)ʲ equals f followed by the upper chart of Y. -/
theorem upperIso_naturality (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    (upperIso E j X).hom ≫ ((raw E j).map f).f j = f ≫ (upperIso E j Y).hom := by
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) j X
  let sY := HomologicalComplex.singleObjXSelf (.up ℤ) j Y
  let u := HomologicalComplex.homotopyCofiber.inrX
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj X)) j
  let v := HomologicalComplex.homotopyCofiber.inrX
    (𝟙 ((HomologicalComplex.single E (.up ℤ) j).obj Y)) j
  have hs : sX.inv ≫ ((HomologicalComplex.single E (.up ℤ) j).map f).f j = f ≫ sY.inv :=
    ((HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).inv.naturality f).symm
  have hm : u ≫ ((raw E j).map f).f j =
      ((HomologicalComplex.single E (.up ℤ) j).map f).f j ≫ v :=
    HomologicalComplex.homotopyCofiber.inrX_mapArrowHom
      (fun k => ⟨k - 1, by change k - 1 + 1 = k; omega⟩) ((singleArrow E j).map f) j
  calc
    _ = (sX.inv ≫ u) ≫ ((raw E j).map f).f j :=
      congrArg (fun g => g ≫ ((raw E j).map f).f j) (upperIso_hom E j X)
    _ = sX.inv ≫ (u ≫ ((raw E j).map f).f j) := Category.assoc _ _ _
    _ = sX.inv ≫ (((HomologicalComplex.single E (.up ℤ) j).map f).f j ≫ v) :=
      congrArg (fun g => sX.inv ≫ g) hm
    _ = (sX.inv ≫ ((HomologicalComplex.single E (.up ℤ) j).map f).f j) ≫ v :=
      (Category.assoc _ _ _).symm
    _ = (f ≫ sY.inv) ≫ v := congrArg (fun g => g ≫ v) hs
    _ = f ≫ (sY.inv ≫ v) := Category.assoc _ _ _
    _ = _ := congrArg (fun g => f ≫ g) (upperIso_hom E j Y).symm

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The degree-j−1
component of Dʲ(f) is lowerChart_X⁻¹≫f≫lowerChart_Y. -/
theorem raw_map_f_lower (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((raw E j).map f).f (j - 1) = (lowerIso E j X).inv ≫ f ≫ (lowerIso E j Y).hom := by
  apply (cancel_epi (lowerIso E j X).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using lowerIso_naturality E j f

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The degree-j
component of Dʲ(f) is upperChart_X⁻¹≫f≫upperChart_Y. -/
theorem raw_map_f_upper (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((raw E j).map f).f j = (upperIso E j X).inv ≫ f ≫ (upperIso E j Y).hom := by
  apply (cancel_epi (upperIso E j X).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using upperIso_naturality E j f

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The functor Dʲ
is additive: Dʲ(f+g)=Dʲ(f)+Dʲ(g). -/
instance raw_additive (j : ℤ) : (raw E j).Additive where
  map_add {X Y} f g := by
    ext p
    by_cases hLower : p = j - 1
    · subst p
      have hAdd : (lowerIso E j X).inv ≫ (f + g) ≫ (lowerIso E j Y).hom =
          (lowerIso E j X).inv ≫ f ≫ (lowerIso E j Y).hom +
            (lowerIso E j X).inv ≫ g ≫ (lowerIso E j Y).hom := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      have hRight : ((raw E j).map f + (raw E j).map g).f (j - 1) =
          (lowerIso E j X).inv ≫ f ≫ (lowerIso E j Y).hom +
            (lowerIso E j X).inv ≫ g ≫ (lowerIso E j Y).hom :=
        (HomologicalComplex.add_f_apply _ _ (j - 1)).trans
          (congrArg₂ (fun u v => u + v) (raw_map_f_lower E j f) (raw_map_f_lower E j g))
      exact (raw_map_f_lower E j (f + g)).trans (hAdd.trans hRight.symm)
    by_cases hUpper : p = j
    · subst p
      have hAdd : (upperIso E j X).inv ≫ (f + g) ≫ (upperIso E j Y).hom =
          (upperIso E j X).inv ≫ f ≫ (upperIso E j Y).hom +
            (upperIso E j X).inv ≫ g ≫ (upperIso E j Y).hom := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      have hRight : ((raw E j).map f + (raw E j).map g).f j =
          (upperIso E j X).inv ≫ f ≫ (upperIso E j Y).hom +
            (upperIso E j X).inv ≫ g ≫ (upperIso E j Y).hom :=
        (HomologicalComplex.add_f_apply _ _ j).trans
          (congrArg₂ (fun u v => u + v) (raw_map_f_upper E j f) (raw_map_f_upper E j g))
      exact (raw_map_f_upper E j (f + g)).trans (hAdd.trans hRight.symm)
    exact (isZero_X E j X p hLower hUpper).eq_of_src _ _

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Evaluation of
Dʲ at degree j−1 is naturally isomorphic to the identity functor of E, via the lower term
charts. -/
def compEvalLowerIso (j : ℤ) : raw E j ⋙ HomologicalComplex.eval E (.up ℤ) (j - 1) ≅ 𝟭 E :=
  NatIso.ofComponents (fun X => (lowerIso E j X).symm) (fun f => by
    change ((raw E j).map f).f (j - 1) ≫ (lowerIso E j _).inv = (lowerIso E j _).inv ≫ f
    rw [raw_map_f_lower]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Evaluation of
Dʲ at degree j is naturally isomorphic to the identity functor of E, via the upper term charts. -/
def compEvalUpperIso (j : ℤ) : raw E j ⋙ HomologicalComplex.eval E (.up ℤ) j ≅ 𝟭 E :=
  NatIso.ofComponents (fun X => (upperIso E j X).symm) (fun f => by
    change ((raw E j).map f).f j ≫ (upperIso E j _).inv = (upperIso E j _).inv ≫ f
    rw [raw_map_f_upper]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. If p differs
from j−1 and j, the functor evaluating Dʲ at p is zero. -/
theorem isZero_compEval (j p : ℤ) (hLower : p ≠ j - 1) (hUpper : p ≠ j) :
    IsZero (raw E j ⋙ HomologicalComplex.eval E (.up ℤ) p) :=
  Functor.isZero _ (fun X => isZero_X E j X p hLower hUpper)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The functor Dʲ
preserves every existing pushout of E-morphisms, by its two natural identity-term charts and
zero evaluations elsewhere. -/
instance raw_preservesPushouts (j : ℤ) : PreservesColimitsOfShape WalkingSpan (raw E j) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun p => by
    by_cases hLower : p = j - 1
    · subst p
      exact preservesColimitsOfShape_of_natIso (compEvalLowerIso E j).symm
    by_cases hUpper : p = j
    · subst p
      exact preservesColimitsOfShape_of_natIso (compEvalUpperIso E j).symm
    exact Functor.preservesColimitsOfShape_of_isZero _
      (isZero_compEval E j p hLower hUpper) WalkingSpan)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. A given pushout
square in E maps to a pushout square of integer cochains under Dʲ, with the same images of all
four legs. -/
theorem raw_map_isPushout (j : ℤ) {X Y Z P : E}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) :
    IsPushout ((raw E j).map i) ((raw E j).map f)
      ((raw E j).map inY) ((raw E j).map inZ) := hP.map (raw E j)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The disk is
bounded with support in [j−1,j]. -/
theorem raw_bounded (j : ℤ) (X : E) : CochainComplex.bounded E ((raw E j).obj X) := by
  refine ⟨j - 1, j, ?_⟩
  intro p hp
  exact isZero_X E j X p (by omega) (by omega)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Regard Dʲ(X) as
a bounded complex using its two-degree support; this gives a functor E→Bounded(E). -/
def bounded (j : ℤ) : E ⥤ Bounded E :=
  ObjectProperty.lift (CochainComplex.bounded E) (raw E j) (raw_bounded E j)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Forgetting the
bounded-disk functor to raw cochains gives Dʲ itself. -/
theorem bounded_comp_ι (j : ℤ) : bounded E j ⋙ ι E = raw E j := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For a≤j−1 and
j≤b, the support of Dʲ(X) is contained in [a,b]. -/
theorem window_support (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) (X : E) :
    windowSupport E a b ((bounded E j).obj X) := by
  intro p hp
  exact isZero_X E j X p (by omega) (by omega)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For a≤j−1 and
j≤b, the disk functor lifts to the full category of cochains supported in [a,b]. -/
def window (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) : E ⥤ Window E a b :=
  ObjectProperty.lift (windowSupport E a b) (bounded E j)
    (window_support E a b j hLower hUpper)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. For a≤j−1 and
j≤b, forgetting the supported disk through the window and bounded inclusions recovers the same
raw Dʲ. -/
theorem window_comp_raw (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) :
    window E a b j hLower hUpper ⋙ windowRaw E a b = raw E j := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. The
identity-cofiber contraction gives a cochain homotopy from id_(Dʲ(X)) to zero. -/
def contraction (j : ℤ) (X : E) : _root_.Homotopy (𝟙 ((raw E j).obj X)) 0 := by
  have h : _root_.Homotopy (𝟙 ((raw E j).obj (((single E j).obj X).obj.X j))) 0 :=
    TruncationAt.topDiskContraction (b := j) ((single E j).obj X)
  have he : (raw E j).obj (((single E j).obj X).obj.X j) = (raw E j).obj X :=
    congrArg (raw E j).obj (HomologicalComplex.single_obj_X_self (.up ℤ) j X)
  exact he ▸ h

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Applying F to the disk contraction shows that F(Dʲ(X)) is acyclic. -/
theorem map_acyclic (j : ℤ) (X : E) :
    ((F.mapHomologicalComplex (.up ℤ)).obj ((raw E j).obj X)).Acyclic := by
  have h : ((F.mapHomologicalComplex (.up ℤ)).obj
      ((raw E j).obj (((single E j).obj X).obj.X j))).Acyclic :=
    TruncationAt.topDisk_map_acyclic (b := j) F ((single E j).obj X)
  have he : (raw E j).obj (((single E j).obj X).obj.X j) = (raw E j).obj X :=
    congrArg (raw E j).obj (HomologicalComplex.single_obj_X_self (.up ℤ) j X)
  exact he ▸ h

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. The supported disk Dʲ(X), whose F-image is
acyclic, defines a functor into the ambient-acyclic [a,b] window. -/
def ambient (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) :
    E ⥤ AmbientAcyclicWindow F a b :=
  ObjectProperty.lift (ambientAcyclicWindowObjects F a b) (window E a b j hLower hUpper)
    (map_acyclic E F j)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. Forgetting the ambient-acyclic support
conditions gives the same raw identity-disk functor Dʲ. -/
theorem ambient_comp_raw (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) :
    ambient E F a b j hLower hUpper ⋙ ambientAcyclicWindowRaw F a b = raw E j := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. The raw map underlying the ambient disk
image of f:X→Y is Dʲ(f). -/
theorem ambient_map_raw (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b)
    {X Y : E} (f : X ⟶ Y) :
    ((ambient E F a b j hLower hUpper).map f).hom.hom.hom = (raw E j).map f := rfl

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. If X is zero in E, its supported ambient
identity disk is zero in the acyclic window category. -/
theorem ambient_map_isZero (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b)
    (X : E) (hX : IsZero X) : IsZero ((ambient E F a b j hLower hUpper).obj X) :=
  IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowRaw F a b) _
    ((raw E j).map_isZero hX)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. The disk on the selected zero of E is
isomorphic to the selected zero of the acyclic support window. -/
def ambientZeroIso (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) :
    (ambient E F a b j hLower hUpper).obj (0 : E) ≅ (0 : AmbientAcyclicWindow F a b) :=
  (ambient_map_isZero E F a b j hLower hUpper (0 : E) (isZero_zero E)).isoZero

variable [ExactCategory E]

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Assume E has an
exact structure. If f:X→Y is an admissible mono, every component Dʲ(f)ᵖ is an admissible mono. -/
theorem raw_map_isAdmissibleMono_f (j : ℤ) {X Y : E} (f : X ⟶ Y)
    (hf : IsAdmissibleMono f) (p : ℤ) : IsAdmissibleMono (((raw E j).map f).f p) := by
  by_cases hLower : p = j - 1
  · subst p
    rw [raw_map_f_lower]
    exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso (lowerIso E j X).inv)
      (admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso (lowerIso E j Y).hom))
  by_cases hUpper : p = j
  · subst p
    rw [raw_map_f_upper]
    exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso (upperIso E j X).inv)
      (admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso (upperIso E j Y).hom))
  let e := (isZero_X E j X p hLower hUpper).isoZero
  have h : IsAdmissibleMono (e.inv ≫ ((raw E j).map f).f p) := IsAdmissibleMono.fromZero _
  have hc : IsAdmissibleMono (e.hom ≫ (e.inv ≫ ((raw E j).map f).f p)) :=
    admissibleMono_comp.comp_mem e.hom _ (IsAdmissibleMono.of_isIso e.hom) h
  simpa only [Iso.hom_inv_id_assoc] using hc

variable [F.IsExact]

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. Assume E has an exact structure and F is
exact; use admissible-mono cofibrations in E and degreewise admissible cofibrations in the
F-acyclic window. An admissible mono f:X→Y induces a cofibration between the supported ambient
identity disks. -/
theorem ambient_map_isCofibration (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b)
    {X Y : E} (f : X ⟶ Y) (hf : IsAdmissibleMono f) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsCofibration ((ambient E F a b j hLower hUpper).map f) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
  exact raw_map_isAdmissibleMono_f E j f hf

omit [ExactCategory E] [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. A given pushout square in E maps to a
pushout of supported ambient identity disks in the F-acyclic window category. -/
theorem ambient_map_isPushout (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b)
    {X Y Z P : E} {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) :
    IsPushout ((ambient E F a b j hLower hUpper).map i)
      ((ambient E F a b j hLower hUpper).map f)
      ((ambient E F a b j hLower hUpper).map inY)
      ((ambient E F a b j hLower hUpper).map inZ) :=
  IsPushout.of_map_of_faithful (ambientAcyclicWindowRaw F a b) (raw_map_isPushout E j hP)

/-- Let E be preadditive with a zero object and binary biproducts, and j∈ℤ. Write Dʲ(X) for the
homotopy cofiber of the identity of the single cochain complex on X in degree j. Let A be
abelian and F:E→A additive. Fix bounds a≤j−1 and j≤b. Assume E has an exact structure and F is
exact; use admissible-mono cofibrations in E and degreewise admissible cofibrations in the
F-acyclic window. The supported identity-disk functor E→C(a,b) is Waldhausen exact for the
exact-category source model and the isomorphism-weak window model. -/
theorem ambient_isWaldhausenExact (a b j : ℤ) (hLower : a ≤ j - 1) (hUpper : j ≤ b) :
    letI := ExactCategory.waldhausenCategory E
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    (ambient E F a b j hLower hUpper).IsWaldhausenExact := by
  let _ := ExactCategory.waldhausenCategory E
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact ambient_map_isZero E F a b j hLower hUpper X hX
  · intro X Y f hf
    change IsAdmissibleMono f at hf
    exact ambient_map_isCofibration E F a b j hLower hUpper f hf
  · intro X Y f hf
    change IsIso f at hf
    let _ : IsIso f := hf
    exact (ambientAcyclicWindow_isWeakEquivalence_iff F a b _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    exact ambient_map_isPushout E F a b j hLower hUpper hP

end CochainComplex.Bounded.SignedDisk

end
