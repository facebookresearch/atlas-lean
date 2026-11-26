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

/-- Let C be abelian, Z an object and K an integer cochain complex. Write F_Z=Hom_C(Z,−), valued in
abelian groups, and H_Z(K)=HomComplex(Z[0],K). There is a canonical isomorphism F_Z(K) ≅ H_Z(K)
of cochain complexes. In degree n it sends f : Z → K^n to the homogeneous cochain from Z[0] with
sole possibly nonzero component f; both differentials are f ↦ f ≫ d_K. -/
def mappedComplexIsoHomSingle (Z : C) (K : CochainComplex C ℤ) :
    ((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := Z) (K := K) (p := 0) (q := n) (n := n) (zero_add n)).symm.toAddCommGrpIso)
    (fun i j hij => ?_)
  ext f
  exact CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)

/-- Let C be abelian, Z an object, K an integer cochain complex and n ∈ ℤ. The degree-n component of
F_Z(K) ≅ HomComplex(Z[0],K) sends f : Z → K^n to the degree-n homogeneous cochain determined by
f at source degree zero, namely fromSingleMk f. -/
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

/-- Let C be abelian, Z an object and g : K → L a map of integer cochain complexes. Postcomposition
gives a cochain map HomComplex(Z[0],K) → HomComplex(Z[0],L). In degree n it sends a homogeneous
cochain θ to the composite of θ with the degree-zero cochain associated to g. -/
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

/-- Let C be abelian, Z an object and g : K → L a cochain map. If e_K : F_Z(K) ≅ HomComplex(Z[0],K)
and e_L are the canonical comparisons, then F_Z(g) ≫ e_L.hom = e_K.hom ≫
homComplexPostcompSingle(Z,g). -/
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

/-- Let C be abelian, K,L integer cochain complexes and q ∈ ℤ. The additive map
originalCycleClassMap sends a degree-q cocycle z in HomComplex(K,L) to its canonical class in
H^q(HomComplex(K,L)), using the cycle inclusion and cycle-to-homology projection. -/
def originalCycleClassMap : AddCommGrpCat.of (Cocycle K L q) ⟶ (HomComplex K L).homology q :=
  (leftHomologyData K L q).π ≫ (leftHomologyData K L q).homologyIso.inv

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, K,L integer cochain complexes, q ∈ ℤ and z a degree-q Hom-complex cocycle. The
additive equivalence homologyAddEquiv sends originalCycleClassMap(z) to CohomologyClass.mk(z),
the class of z modulo homogeneous coboundaries. -/
theorem homologyAddEquiv_originalCycleClass (z : Cocycle K L q) :
    homologyAddEquiv K L q (originalCycleClassMap K L q z) = CohomologyClass.mk z := by
  have h : originalCycleClassMap K L q ≫ (leftHomologyData K L q).homologyIso.hom =
      (leftHomologyData K L q).π := by
    dsimp only [originalCycleClassMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h z

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, K,L integer cochain complexes and q ∈ ℤ. The map from degree-q cocycles to
H^q(HomComplex(K,L)) is the composite of the lift to cycles of the forgetful map z ↦ z.val and
the canonical homology projection π_q. The cocycle equation δz=0 supplies this lift. -/
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

/-- Let D be a preadditive category, X an object and e : Y ≅ Z an isomorphism. Postcomposition with
e.hom gives the additive equivalence Hom_D(X,Y) ≅ Hom_D(X,Z), with inverse postcomposition by
e.inv. -/
def homPostcompAddEquiv {D : Type*} [Category* D] [Preadditive D]
    (X : D) {Y Z : D} (e : Y ≅ Z) : (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := (Category.assoc f e.hom e.inv).trans
    ((congrArg (fun a => f ≫ a) e.hom_inv_id).trans (Category.comp_id f))
  right_inv f := (Category.assoc f e.inv e.hom).trans
    ((congrArg (fun a => f ≫ a) e.inv_hom_id).trans (Category.comp_id f))
  map_add' f g := @CategoryTheory.Preadditive.add_comp D _ _ X Y Z f g e.hom

/-- Let C be abelian, K,L integer cochain complexes and q ∈ ℤ. There is an additive equivalence
H^q(HomComplex(K,L)) ≅ Hom_{K(C)}([K],[L][q]), where K(C) is the homotopy category of integer
cochain complexes. It sends the class of a cocycle to the quotient class of the corresponding
cochain map K → L[q], followed by the quotient shift comparison. -/
def homologyShiftedHomEquiv (K L : CochainComplex C ℤ) (q : ℤ) :
    (HomComplex K L).homology q ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        ((HomotopyCategory.quotient C (.up ℤ)).obj L)⟦q⟧) :=
  (homologyAddEquiv K L q).trans
    ((CohomologyClass.homAddEquiv (K := K) (L := L) (n := q)).trans
      (homPostcompAddEquiv ((HomotopyCategory.quotient C (.up ℤ)).obj K)
        (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso q).app L)))

/-- Let C be abelian, K,L integer cochain complexes, q ∈ ℤ and z a degree-q cocycle from K to L. The
shifted-Hom equivalence sends originalCycleClassMap(z) to z.shiftedHom : [K] → [L][q] in the
homotopy category, retaining the cochain map represented by z. -/
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
/-- Let C be abelian, Z an object, g : K → L a cochain map and q ∈ ℤ. For a degree-q cocycle z from
Z[0] to K, the homology map induced by homComplexPostcompSingle(Z,g) sends [z] to the canonical
class of z postcomposed with g. -/
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

/-- Let C be abelian, K,L integer cochain complexes and q ∈ ℤ. The canonical class map from degree-q
cocycles to H^q(HomComplex(K,L)) is surjective: every homology class is represented by a cocycle
z. -/
theorem originalCycleClassMap_surjective (K L : CochainComplex C ℤ) (q : ℤ) :
    Function.Surjective (originalCycleClassMap K L q) := by
  intro x
  obtain ⟨z, hz⟩ := (homologyAddEquiv K L q x).mk_surjective
  refine ⟨z, ?_⟩
  apply (homologyAddEquiv K L q).injective
  rw [homologyAddEquiv_originalCycleClass]
  exact hz

/-- Let C be abelian, Z an object, g : K → L a cochain map, q ∈ ℤ and x ∈ H^q(HomComplex(Z[0],K)).
Under the shifted-Hom equivalences, the image of x by H^q(homComplexPostcompSingle(Z,g)) is the
shifted homotopy morphism representing x followed by [g][q] : [K][q] → [L][q]. -/
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

/-- Let C be abelian, Z an object, K an integer cochain complex and a ∈ ℤ. There is a canonical
cochain-complex isomorphism h_{a,K} : HomComplex(Z[0],K)[a] ≅ HomComplex(Z[0],K[a]). Its
degree-q terms identify Hom_C(Z,K^{q+a}) on both sides and preserve the signed shift
differential. -/
def homSingleShiftIso (Z : C) (K : CochainComplex C ℤ) (a : ℤ) :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧ ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) :=
  (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) a).mapIso (mappedComplexIsoHomSingle Z K).symm ≪≫
    (((preadditiveCoyoneda.obj (Opposite.op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso a).symm.app K ≪≫
      mappedComplexIsoHomSingle Z (K⟦a⟧)

/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. For f : Z → K^{q+a},
the degree-q component of h_{a,K} sends the homogeneous cochain from Z[0] to K of degree q+a
determined by f to the degree-q cochain from Z[0] to K[a] determined by that same f. -/
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

/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. The map u from degree-q
cocycles of HomComplex(Z[0],K[a]) to HomComplex(Z[0],K)[a]^q first forgets the cocycle condition
and then applies the inverse degree-q component of h_{a,K}. -/
def homSingleShiftCycleInclusion (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    AddCommGrpCat.of (CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧) q) ⟶
      ((CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)⟦a⟧).X q :=
  AddCommGrpCat.ofHom (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom _ _ q) ≫
    (homSingleShiftIso Z K a).inv.f q

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. The transported
inclusion u = homSingleShiftCycleInclusion satisfies u ≫ d_{HomComplex(Z[0],K)[a],q,q+1} = 0, so
its values lie in the cycles of the shifted Hom complex. -/
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
/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. Write h :
HomComplex(Z[0],K)[a] ≅ HomComplex(Z[0],K[a]) and u for the transported cocycle inclusion. The
canonical cycle-class map into H^q(HomComplex(Z[0],K[a])) followed by H^q(h.inv) equals
liftCycles(u) followed by the homology projection of HomComplex(Z[0],K)[a]. -/
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
/-- Let C be abelian, K an integer cochain complex, a,q ∈ ℤ and f : A → K[a]^q satisfy f ≫
d_{K[a],q,q+1} = 0. Let s : H^q(K[a]) ≅ H^{q+a}(K) be the canonical homology shift and τ₂ :
K[a]^q → K^{q+a} the middle component of the shifted short-complex comparison. Then
liftCycles(f) ≫ π_K[a],q ≫ s.hom = liftCycles(f ≫ τ₂) ≫ π_K,q+a. -/
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
/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. Follow the inclusion of
degree-q cocycles of HomComplex(Z[0],K[a]) into HomComplex(Z[0],K)[a]^q by the middle component
of its homology-shift short-complex comparison. The resulting map sends z to the underlying
degree-(q+a) cochain of z.rightUnshift, from Z[0] to K. -/
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

/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. The isomorphism χ_{a,q}
: H^q(HomComplex(Z[0],K[a])) ≅ H^{q+a}(HomComplex(Z[0],K)) is induced by the inverse of h_{a,K},
followed by the canonical homology shift of the complex HomComplex(Z[0],K). -/
def homSingleShiftHomologyIso (Z : C) (K : CochainComplex C ℤ) (a q : ℤ) :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) (K⟦a⟧)).homology q ≅
      (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K).homology (q + a) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) q).mapIso
      (homSingleShiftIso Z K a).symm ≪≫
    (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{v} a q (q + a)
      (by omega)).app (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj Z) K)

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. If z is a degree-q
cocycle from Z[0] to K[a], then χ_{a,q} sends its canonical class to the canonical class of
z.rightUnshift, a degree-(q+a) cocycle from Z[0] to K. -/
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

/-- Let C be abelian, Z an object, T a triangle of integer cochain complexes with d : T₃ → T₁[1], q
∈ ℤ and x ∈ H^q(HomComplex(Z[0],T₃)). Write ψ for the shifted-Hom equivalence and χ for the
single-Hom target-shift comparison. Then ψ_{T₁,q+1}(χ_{1,q}(H^q(postcomp(d))(x))) equals the
degree-q-to-(q+1) boundary of Hom_{K(C)}([Z[0]],−) on the quotient triangle applied to
ψ_{T₃,q}(x). It uses the actual map d and shift-add order 1,q. -/
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

/-- Let C be abelian, Z an object, K an integer cochain complex and a ∈ ℤ. Write e_K : F_Z(K) ≅
HomComplex(Z[0],K), h_{a,K} for the single-Hom shift isomorphism and σ_{a,K} : F_Z(K[a]) ≅
F_Z(K)[a] for the Coyoneda shift comparison. Then e_{K[a]}.hom ≫ h_{a,K}.inv = σ_{a,K}.hom ≫
e_K.hom[a] as cochain maps. -/
theorem mappedComplexIsoHomSingle_shift (Z : C) (K : CochainComplex C ℤ) (a : ℤ) :
    (mappedComplexIsoHomSingle Z (K⟦a⟧)).hom ≫ (homSingleShiftIso Z K a).inv =
      (((preadditiveCoyoneda.obj (op Z)).mapHomologicalComplex (.up ℤ)).commShiftIso a).hom.app K ≫
        (mappedComplexIsoHomSingle Z K).hom⟦a⟧' := by
  simp [homSingleShiftIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, Z an object, K an integer cochain complex and a,q ∈ ℤ. Let e_K : F_Z(K) ≅
HomComplex(Z[0],K), σ : F_Z(K[a]) ≅ F_Z(K)[a], s : H^q(F_Z(K)[a]) ≅ H^{q+a}(F_Z(K)) and χ :
H^q(HomComplex(Z[0],K[a])) ≅ H^{q+a}(HomComplex(Z[0],K)) be the canonical comparisons. Then
H^q(e_{K[a]}.hom) ≫ χ.hom = H^q(σ.hom) ≫ s.hom ≫ H^{q+a}(e_K.hom). -/
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
/-- Let C be abelian, Z an object, T a triangle of integer cochain complexes with d : T₃ → T₁[1], q
∈ ℤ and x ∈ H^q(F_Z(T₃)), where F_Z=Hom_C(Z,−). Apply H^q(F_Z(d)), then the Coyoneda shift
comparison H^q(F_Z(T₁[1])) → H^q(F_Z(T₁)[1]), and the homology shift to degree q+1. Under F_Z(K)
≅ HomComplex(Z[0],K) and the shifted-Hom equivalence, this result is the covariant Hom boundary
of the quotient triangle applied to the shifted homotopy morphism representing x. Every arrow
uses the actual third map d and the canonical shift comparisons. -/
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
