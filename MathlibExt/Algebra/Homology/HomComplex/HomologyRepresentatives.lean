/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import MathlibExt.Algebra.Homology.HomComplex.CocycleBoundary
public import MathlibExt.Algebra.Homology.ShortComplex.CycleClassProjection
public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyoneda

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original degreewise Coyoneda complex is literally the Hom complex
from the original degree-zero single object. -/
def mappedComplexIsoHomSingle (Z : C) (K : CochainComplex C ℤ) :
    ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := Z) (K := K) (p := 0) (q := n) (n := n) (zero_add n)).symm.toAddCommGrpIso)
    (fun i j hij => ?_)
  ext f
  exact CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)

/-- Every component is the original from-single cochain. -/
@[simp] theorem mappedComplexIsoHomSingle_hom_apply (Z : C)
    (K : CochainComplex C ℤ) (n : ℤ) (f : Z ⟶ K.X n) :
    @DFunLike.coe
      ((Z ⟶ K.X n) →+ CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor C 0).obj Z) K n)
      (Z ⟶ K.X n)
      (fun _ => CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor C 0).obj Z) K n)
      AddMonoidHom.instFunLike
      (ConcreteCategory.hom ((mappedComplexIsoHomSingle Z K).hom.f n)) f =
      CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n) := rfl

/-- The Hom-complex map is postcomposition with the given chain map. -/
def homComplexPostcompSingle (Z : C) {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K ⟶
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) L where
  f n := AddCommGrpCat.ofHom {
    toFun := fun z => z.comp (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n)
    map_zero' := by simp
    map_add' := fun z z' => CochainComplex.HomComplex.Cochain.add_comp z z'
      (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n) }
  comm' i j hij := by
    ext z
    exact CochainComplex.HomComplex.δ_comp_ofHom z g j

/-- The same single-Hom comparison is natural in every chain map. -/
theorem mappedComplexIsoHomSingle_naturality (Z : C)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map g ≫
        (mappedComplexIsoHomSingle Z L).hom =
      (mappedComplexIsoHomSingle Z K).hom ≫ homComplexPostcompSingle Z g := by
  ext n f
  exact CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp f (zero_add n) g

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K L : CochainComplex C ℤ) (q : ℤ)

/-- The original Hom-complex cycle class, through its homology data. -/
def originalCycleClassMap : AddCommGrpCat.of (Cocycle K L q) ⟶ (HomComplex K L).homology q :=
  (leftHomologyData K L q).π ≫ (leftHomologyData K L q).homologyIso.inv

set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison maps every original cycle to its same class. -/
theorem homologyAddEquiv_originalCycleClass (z : Cocycle K L q) :
    homologyAddEquiv K L q (originalCycleClassMap K L q z) = CohomologyClass.mk z := by
  have h : originalCycleClassMap K L q ≫ (leftHomologyData K L q).homologyIso.hom =
      (leftHomologyData K L q).π := by
    dsimp only [originalCycleClassMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h z

set_option backward.isDefEq.respectTransparency false in
/-- Every cycle is represented by the original lift and homology projection. -/
theorem originalCycleClassMap_eq :
    originalCycleClassMap K L q =
      ((HomComplex K L).sc q).liftCycles
        (AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L q))
        (by ext z; exact z.δ_eq_zero _) ≫ (HomComplex K L).homologyπ q := by
  let S := (HomComplex K L).sc q
  let h := leftHomologyData K L q
  dsimp only [originalCycleClassMap]
  rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  have hh : S.liftCycles h.i h.wi = h.cyclesIso.inv := by
    apply (cancel_mono S.iCycles).1
    rw [ShortComplex.liftCycles_i, h.cyclesIso_inv_comp_iCycles]
  rw [← hh]
  rfl

end CochainComplex.HomComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Postcomposition by an isomorphism as an additive Hom equivalence. -/
def homPostcompAddEquiv {D : Type*} [Category* D] [Preadditive D]
    (X : D) {Y Z : D} (e : Y ≅ Z) : (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := (Category.assoc f e.hom e.inv).trans
    ((congrArg (fun a => f ≫ a) e.hom_inv_id).trans (Category.comp_id f))
  right_inv f := (Category.assoc f e.inv e.hom).trans
    ((congrArg (fun a => f ≫ a) e.inv_hom_id).trans (Category.comp_id f))
  map_add' f g := @CategoryTheory.Preadditive.add_comp D _ _ X Y Z f g e.hom

/-- Hom-complex homology is represented by the SAME shifted homotopy morphism. -/
def homologyShiftedHomEquiv (K L : CochainComplex C ℤ) (q : ℤ) :
    (HomComplex K L).homology q ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        ((HomotopyCategory.quotient C (.up ℤ)).obj L)⟦q⟧) :=
  (homologyAddEquiv K L q).trans
    ((CohomologyClass.homAddEquiv (K := K) (L := L) (n := q)).trans
      (homPostcompAddEquiv ((HomotopyCategory.quotient C (.up ℤ)).obj K)
        (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso q).app L)))

/-- Every original cocycle keeps its literal quotient representative. -/
theorem homologyShiftedHomEquiv_originalCycleClass
    (K L : CochainComplex C ℤ) (q : ℤ) (z : Cocycle K L q) :
    homologyShiftedHomEquiv K L q (originalCycleClassMap K L q z) = z.shiftedHom := by
  rw [homologyShiftedHomEquiv, AddEquiv.trans_apply, homologyAddEquiv_originalCycleClass]
  rfl

end CochainComplex.HomComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The homology arrow sends every original cocycle to the same postcomposed cycle. -/
theorem originalCycleClassMap_postcomp (Z : C) {K L : CochainComplex C ℤ}
    (g : K ⟶ L) (q : ℤ)
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj Z) K q) :
    HomologicalComplex.homologyMap (CategoryTheory.DerivedCoyoneda.homComplexPostcompSingle Z g) q
      (originalCycleClassMap _ K q z) =
        originalCycleClassMap _ L q (z.postcomp g) := by
  let A := HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K
  let B := HomComplex ((CochainComplex.singleFunctor C 0).obj Z) L
  let f := CategoryTheory.DerivedCoyoneda.homComplexPostcompSingle Z g
  have h : originalCycleClassMap _ K q ≫ HomologicalComplex.homologyMap f q =
      AddCommGrpCat.ofHom {
        toFun := fun z => z.postcomp g
        map_zero' := by apply Cocycle.ext; simp
        map_add' := fun z z' => by apply Cocycle.ext; simp } ≫ originalCycleClassMap _ L q := by
    rw [originalCycleClassMap_eq, originalCycleClassMap_eq]
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc]
    dsimp only [HomologicalComplex.cyclesMap]
    rw [ShortComplex.liftCycles_comp_cyclesMap]
    have hc : (B.sc q).liftCycles
        (AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom ((singleFunctor C 0).obj Z) K q) ≫
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) q).map f).τ₂)
        (by ext z; exact (z.postcomp g).δ_eq_zero _) =
      AddCommGrpCat.ofHom {
        toFun := fun z => z.postcomp g
        map_zero' := by apply Cocycle.ext; simp
        map_add' := fun z z' => by apply Cocycle.ext; simp } ≫
        (B.sc q).liftCycles
          (AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom ((singleFunctor C 0).obj Z) L q))
          (by ext z; exact z.δ_eq_zero _) := by
      apply (cancel_mono (B.iCycles q)).1
      change _ ≫ (B.sc q).iCycles = _ ≫ _ ≫ (B.sc q).iCycles
      simp only [ShortComplex.liftCycles_i]
      rfl
    exact congrArg (fun a => a ≫ B.homologyπ q) hc
  exact ConcreteCategory.congr_hom h z

/-- Every original homology class has an cocycle representative. -/
theorem originalCycleClassMap_surjective (K L : CochainComplex C ℤ) (q : ℤ) :
    Function.Surjective (originalCycleClassMap K L q) := by
  intro x
  obtain ⟨z, hz⟩ := (homologyAddEquiv K L q x).mk_surjective
  refine ⟨z, ?_⟩
  apply (homologyAddEquiv K L q).injective
  rw [homologyAddEquiv_originalCycleClass]
  exact hz

/-- The SAME homology representative comparison is natural under postcomposition. -/
theorem homologyShiftedHomEquiv_postcomp (Z : C) {K L : CochainComplex C ℤ}
    (g : K ⟶ L) (q : ℤ)
    (x : (HomComplex ((singleFunctor C 0).obj Z) K).homology q) :
    homologyShiftedHomEquiv ((singleFunctor C 0).obj Z) L q
      (HomologicalComplex.homologyMap (CategoryTheory.DerivedCoyoneda.homComplexPostcompSingle Z g) q x) =
      homologyShiftedHomEquiv ((singleFunctor C 0).obj Z) K q x ≫
        ((HomotopyCategory.quotient C (.up ℤ)).map g)⟦q⟧' := by
  obtain ⟨z, rfl⟩ := originalCycleClassMap_surjective ((singleFunctor C 0).obj Z) K q x
  rw [originalCycleClassMap_postcomp, homologyShiftedHomEquiv_originalCycleClass,
    homologyShiftedHomEquiv_originalCycleClass]
  dsimp only [Cocycle.shiftedHom]
  rw [Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, Category.assoc]
  exact (congrArg (fun f => (HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.equivHomShift.symm z) ≫ f)
    ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso_hom_naturality g q)).trans
      (Category.assoc _ _ _).symm

end CochainComplex.HomComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The single-source Hom complex shifts by the same coefficient shift. -/
def homSingleShiftIso (Z : C) (K : CochainComplex C ℤ) (a : ℤ) :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧ ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) :=
  (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) a).mapIso (mappedComplexIsoHomSingle Z K).symm ≪≫
    (((preadditiveCoyoneda.obj (Opposite.op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso a).symm.app K ≪≫
      mappedComplexIsoHomSingle Z (K⟦a⟧)

/--
The shift comparison keeps the same original pointwise morphism, encoded as the from-single
cochain on the shifted target.
-/
theorem homSingleShiftIso_hom_fromSingle (Z : C) (K : CochainComplex C ℤ)
    (a q : ℤ) (f : Z ⟶ K.X (q + a)) :
    (homSingleShiftIso Z K a).hom.f q
      (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add (q + a))) =
      CochainComplex.HomComplex.Cochain.fromSingleMk (K := K⟦a⟧)
        (p := 0) (q := q) (n := q) f (zero_add q) := by
  dsimp [homSingleShiftIso, mappedComplexIsoHomSingle, AddEquiv.toAddCommGrpIso]
  change (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := Z) (K := K⟦a⟧) (p := 0) (q := q) (n := q) (zero_add q)).symm
    ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := Z) (K := K) (p := 0) (q := q + a) (n := q + a) (zero_add (q + a)))
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add (q + a)))) = _
  rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  rfl

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The shifted-source cycle inclusion through the SAME single-Hom iso. -/
def homSingleShiftCycleInclusion (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    AddCommGrpCat.of (CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) q) ⟶
      ((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).X q :=
  AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ _ q) ≫
    (homSingleShiftIso Z K a).inv.f q

set_option backward.isDefEq.respectTransparency false in
/-- The real shifted inclusion lands in the cycles. -/
theorem homSingleShiftCycleInclusion_cycle (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    homSingleShiftCycleInclusion Z K a q ≫
      ((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).d q (q + 1) = 0 := by
  dsimp only [homSingleShiftCycleInclusion]
  rw [Category.assoc, (homSingleShiftIso Z K a).inv.comm q (q + 1),
    ← Category.assoc]
  have hz : AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ _ q) ≫
      (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧)).d q (q + 1) = 0 := by
    ext z
    exact z.δ_eq_zero _
  rw [hz, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The Hom(single) inverse carries each cycle to its same shifted cycle class. -/
theorem homSingleShiftCycleClassMap (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    CochainComplex.HomComplex.originalCycleClassMap _ (K⟦a⟧) q ≫
      HomologicalComplex.homologyMap (homSingleShiftIso Z K a).inv q =
    (((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).sc q).liftCycles
      (homSingleShiftCycleInclusion Z K a q)
      (by
        change homSingleShiftCycleInclusion Z K a q ≫
          ((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).d
            q ((ComplexShape.up ℤ).next q) = 0
        have hn : (ComplexShape.up ℤ).next q = q + 1 :=
          ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
        rw [hn]
        exact homSingleShiftCycleInclusion_cycle Z K a q) ≫
        ((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).homologyπ q := by
  rw [CochainComplex.HomComplex.originalCycleClassMap_eq]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  dsimp only [HomologicalComplex.cyclesMap]
  rw [ShortComplex.liftCycles_comp_cyclesMap]
  rfl

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
The stock homology shift sends the shifted cycle projection to the original cycle projection after
the same middle-component shift map.
-/
theorem liftCycles_shiftIso_homologyProjection (K : CochainComplex C ℤ) (a q : ℤ)
    {A : C} (f : A ⟶ (K⟦a⟧).X q) (hf : f ≫ (K⟦a⟧).d q (q + 1) = 0) :
    ((K⟦a⟧).sc q).liftCycles f (by
      have hn : (ComplexShape.up ℤ).next q = q + 1 :=
        ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
      change f ≫ (K⟦a⟧).d q ((ComplexShape.up ℤ).next q) = 0
      rw [hn]; exact hf) ≫ (K⟦a⟧).homologyπ q ≫
        (ShiftSequence.shiftIso C a q (q + a) (by omega)).hom.app K =
      (K.sc (q + a)).liftCycles
        (f ≫ ((shiftShortComplexFunctorIso C a q (q + a) (by omega)).hom.app K).τ₂)
        (by
          have h := ((shiftShortComplexFunctorIso C a q (q + a) (by omega)).hom.app K).comm₂₃
          rw [Category.assoc, h, ← Category.assoc]
          have hn : (ComplexShape.up ℤ).next q = q + 1 :=
            ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
          have hcycle : f ≫ ((K⟦a⟧).sc q).g = 0 := by
            change f ≫ (K⟦a⟧).d q ((ComplexShape.up ℤ).next q) = 0
            rw [hn]
            exact hf
          exact (congrArg (fun z => z ≫
            ((shiftShortComplexFunctorIso C a q (q + a) (by omega)).hom.app K).τ₃)
              hcycle).trans zero_comp) ≫ K.homologyπ (q + a) := by
  let e := (shiftShortComplexFunctorIso C a q (q + a) (by omega)).hom.app K
  have hf' : f ≫ ((K⟦a⟧).sc q).g = 0 := by
    have hn : (ComplexShape.up ℤ).next q = q + 1 :=
      ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
    change f ≫ (K⟦a⟧).d q ((ComplexShape.up ℤ).next q) = 0
    rw [hn]
    exact hf
  exact (congrArg (fun t => ((K⟦a⟧).sc q).liftCycles f hf' ≫
      (K⟦a⟧).homologyπ q ≫ t) (ShiftSequence.shiftIso_hom_app (C := C) a q (q + a) (by omega) K)).trans
    (ShortComplex.liftCycles_homologyMap e f hf')


end CochainComplex

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The SAME shifted cycle inclusion is the original right-unshifted cochain,
with the exact homology shift middle-component transport. -/
theorem homSingleShiftCycleInclusion_original_rightUnshift
    (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    homSingleShiftCycleInclusion Z K a q ≫
        ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v} a q (q + a)
          (by omega)).hom.app
            (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)).τ₂ =
      AddCommGrpCat.ofHom {
        toFun := fun z : CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) q =>
          (z.rightUnshift (q + a) rfl).val
        map_zero' := by
          exact congrArg (fun z => z.val)
            (CochainComplex.HomComplex.Cocycle.rightShiftAddEquiv
              (K := (CochainComplex.singleFunctor C 0).obj Z) (L := K)
              (q + a) a q rfl).symm.map_zero
        map_add' := fun z z' =>
          congrArg (fun z => z.val)
            ((CochainComplex.HomComplex.Cocycle.rightShiftAddEquiv
              (K := (CochainComplex.singleFunctor C 0).obj Z) (L := K)
              (q + a) a q rfl).symm.map_add z z') } := by
  ext z
  obtain ⟨f, hf, hz⟩ := CochainComplex.HomComplex.Cocycle.fromSingleMk_surjective z q (zero_add q) (q + 1) rfl
  subst z
  dsimp [homSingleShiftCycleInclusion, homSingleShiftIso, mappedComplexIsoHomSingle,
    AddEquiv.toAddCommGrpIso, CochainComplex.shiftShortComplexFunctorIso,
    CochainComplex.shiftShortComplexFunctor']
  change CochainComplex.HomComplex.Cochain.fromSingleMk (K := K)
      (p := 0) (q := q + a) (n := q + a)
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
        (X := Z) (K := K⟦a⟧) (p := 0) (q := q) (n := q) (zero_add q))
          (CochainComplex.HomComplex.Cochain.fromSingleMk (K := K⟦a⟧) f (zero_add q)))
      (zero_add (q + a)) =
    ((CochainComplex.HomComplex.Cocycle.fromSingleMk f (zero_add q) (q + 1) rfl hf).rightUnshift (q + a) rfl).val
  rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  exact (CochainComplex.HomComplex.Cochain.fromSingleMk_rightUnshift Z K a q f).symm


end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The single-Hom target shift identifies homology in the shifted complex with original Hom-complex
homology in the same shifted degree.
-/
def homSingleShiftHomologyIso (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧)).homology q ≅
      (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K).homology (q + a) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) q).mapIso
      (homSingleShiftIso Z K a).symm ≪≫
    (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a)
      (by omega)).app (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves the literal original right-unshifted cocycle class. -/
theorem homSingleShiftHomologyIso_originalCycleClass (Z : C)
    (K : CochainComplex C ℤ) (a q : ℤ)
    (z : CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) q) :
    (homSingleShiftHomologyIso Z K a q).hom
      (CochainComplex.HomComplex.originalCycleClassMap _ (K⟦a⟧) q z) =
      CochainComplex.HomComplex.originalCycleClassMap _ K (q + a)
        (z.rightUnshift (q + a) rfl) := by
  let A := CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K
  have hm := homSingleShiftCycleClassMap Z K a q
  have hp := CochainComplex.liftCycles_shiftIso_homologyProjection A a q
    (homSingleShiftCycleInclusion Z K a q) (homSingleShiftCycleInclusion_cycle Z K a q)
  have h := (Category.assoc
    (CochainComplex.HomComplex.originalCycleClassMap _ (K⟦a⟧) q)
    (HomologicalComplex.homologyMap (homSingleShiftIso Z K a).inv q)
    ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a) (by omega)).hom.app A)).symm.trans
      ((congrArg (fun t => t ≫ (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v}
          a q (q + a) (by omega)).hom.app A) hm).trans hp)
  let R := (CochainComplex.HomComplex.Cocycle.rightShiftAddEquiv
      (K := (CochainComplex.singleFunctor C 0).obj Z) (L := K)
      (q + a) a q rfl).symm
  let rmap := AddCommGrpCat.ofHom R.toAddMonoidHom
  have hi := homSingleShiftCycleInclusion_original_rightUnshift Z K a q
  let inc := homSingleShiftCycleInclusion Z K a q ≫
    ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v} a q (q + a)
      (by omega)).hom.app A).τ₂
  have hinc : inc ≫ (A.sc (q + a)).g = 0 := by
    have hin : inc = rmap ≫
        AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ K (q + a)) := hi
    have hc : AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ K (q + a)) ≫
        (A.sc (q + a)).g = 0 := by
      ext y
      exact y.δ_eq_zero _
    exact (congrArg (fun morphism => morphism ≫ (A.sc (q + a)).g) hin).trans
      ((Category.assoc rmap
        (AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ K (q + a)))
        (A.sc (q + a)).g).trans
          ((congrArg (fun morphism => rmap ≫ morphism) hc).trans comp_zero))
  have hr : rmap ≫ CochainComplex.HomComplex.originalCycleClassMap _ K (q + a) =
      (A.sc (q + a)).liftCycles
        (homSingleShiftCycleInclusion Z K a q ≫
          ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v} a q (q + a)
            (by omega)).hom.app A).τ₂) hinc ≫ A.homologyπ (q + a) := by
    rw [CochainComplex.HomComplex.originalCycleClassMap_eq]
    have hcy : rmap ≫ (A.sc (q + a)).liftCycles
          (AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ K (q + a)))
          (by ext y; exact y.δ_eq_zero _) =
        (A.sc (q + a)).liftCycles
          (homSingleShiftCycleInclusion Z K a q ≫
            ((CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat.{v} a q (q + a)
              (by omega)).hom.app A).τ₂) hinc := by
      apply (cancel_mono (A.sc (q + a)).iCycles).1
      simp only [Category.assoc, ShortComplex.liftCycles_i]
      exact hi.symm
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ A.homologyπ (q + a)) hcy)
  exact ConcreteCategory.congr_hom (h.trans hr.symm) z


end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The original Hom-complex homology representative transports the grade-one triangle arrow to the
covariant homotopy-category connector. The target shift and its order are the original ones.
-/
theorem homSingleShiftHomology_boundary (Z : C)
    (T : Triangle (CochainComplex C ℤ)) (q : ℤ)
    (x : (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z)
      T.obj₃).homology q) :
    CochainComplex.HomComplex.homologyShiftedHomEquiv
        ((CochainComplex.singleFunctor C 0).obj Z) T.obj₁ (q + 1)
        ((homSingleShiftHomologyIso Z T.obj₁ 1 q).hom
          (HomologicalComplex.homologyMap
            (homComplexPostcompSingle Z T.mor₃) q x)) =
      (preadditiveCoyoneda.obj (op
          ((HomotopyCategory.quotient C (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj Z)))).homologySequenceδ
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj T)
        q (q + 1) rfl
        (CochainComplex.HomComplex.homologyShiftedHomEquiv
          ((CochainComplex.singleFunctor C 0).obj Z) T.obj₃ q x) := by
  obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.originalCycleClassMap_surjective
    ((CochainComplex.singleFunctor C 0).obj Z) T.obj₃ q x
  rw [CochainComplex.HomComplex.originalCycleClassMap_postcomp,
    homSingleShiftHomologyIso_originalCycleClass,
    CochainComplex.HomComplex.homologyShiftedHomEquiv_originalCycleClass,
    CochainComplex.HomComplex.homologyShiftedHomEquiv_originalCycleClass]
  exact (CochainComplex.HomComplex.Cocycle.shiftedHom_boundary T q z).symm

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The original Coyoneda complex comparison respects the target shift, with its existing coefficient
shift isomorphism.
-/
theorem mappedComplexIsoHomSingle_shift (Z : C) (K : CochainComplex C ℤ) (a : ℤ) :
    (mappedComplexIsoHomSingle Z (K⟦a⟧)).hom ≫ (homSingleShiftIso Z K a).inv =
      (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso a).hom.app K ≫
        (mappedComplexIsoHomSingle Z K).hom⟦a⟧' := by
  simp [homSingleShiftIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The same shift comparison commutes on homology in every integer degree. -/
theorem mappedComplexIsoHomSingle_homology_shift (Z : C)
    (K : CochainComplex C ℤ) (a q : ℤ) :
    HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z (K⟦a⟧)).hom q ≫
        (homSingleShiftHomologyIso Z K a q).hom =
      HomologicalComplex.homologyMap
          ((((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso a).hom.app K) q ≫
        ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a)
          (by omega)).hom.app
          (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj K)) ≫
        HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z K).hom (q + a) := by
  change HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z (K⟦a⟧)).hom q ≫
      HomologicalComplex.homologyMap (homSingleShiftIso Z K a).inv q ≫
      (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a)
        (by omega)).hom.app
        (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K) = _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    mappedComplexIsoHomSingle_shift, HomologicalComplex.homologyMap_comp]
  rw [Category.assoc]
  congr 1
  exact ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a)
    (by omega)).hom.naturality (mappedComplexIsoHomSingle Z K).hom)

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
The mapped Coyoneda triangle arrow, coefficient shift and stock homology shift have the same
covariant connector on original representatives.
-/
theorem mappedCoyoneda_triangle_representative (Z : C)
    (T : Triangle (CochainComplex C ℤ)) (q : ℤ)
    (x : (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj
      T.obj₃).homology q) :
    CochainComplex.HomComplex.homologyShiftedHomEquiv
      ((CochainComplex.singleFunctor C 0).obj Z) T.obj₁ (q + 1)
      (HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z T.obj₁).hom (q + 1)
        (((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} 1 q (q + 1)
          (by omega)).hom.app
          (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj T.obj₁))
          (HomologicalComplex.homologyMap
            ((((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app
              T.obj₁) q
            (HomologicalComplex.homologyMap
              (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map T.mor₃) q x)))) =
      (preadditiveCoyoneda.obj (op
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj Z)))).homologySequenceδ
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj T) q (q + 1) rfl
        (CochainComplex.HomComplex.homologyShiftedHomEquiv
          ((CochainComplex.singleFunctor C 0).obj Z) T.obj₃ q
          (HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z T.obj₃).hom q x)) := by
  have hn := congrArg (fun f => HomologicalComplex.homologyMap f q)
    (mappedComplexIsoHomSingle_naturality Z T.mor₃)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  have hs := mappedComplexIsoHomSingle_homology_shift Z T.obj₁ 1 q
  have h := congrArg (fun f =>
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).map T.mor₃) q ≫ f) hs
  simp only [← Category.assoc] at h
  rw [hn] at h
  have hx := ConcreteCategory.congr_hom h x
  change (homSingleShiftHomologyIso Z T.obj₁ 1 q).hom
      (HomologicalComplex.homologyMap (homComplexPostcompSingle Z T.mor₃) q
        (HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z T.obj₃).hom q x)) = _ at hx
  exact (congrArg
    (CochainComplex.HomComplex.homologyShiftedHomEquiv
      ((CochainComplex.singleFunctor C 0).obj Z) T.obj₁ (q + 1)) hx.symm).trans
        (homSingleShiftHomology_boundary Z T q
          (HomologicalComplex.homologyMap (mappedComplexIsoHomSingle Z T.obj₃).hom q x))

end CategoryTheory.DerivedCoyoneda

end
