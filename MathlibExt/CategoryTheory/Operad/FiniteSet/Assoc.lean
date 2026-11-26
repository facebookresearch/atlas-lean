/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.FiniteSet.Elementwise
public import Mathlib.Order.Sigma

/-!
# Associative collection via linear orders

The associative symmetric collection assigns to each finite type `I`
the type `LinearOrder I` of linear orders. Morphisms act by covariant
transport `e.symm.linearOrder`, so `x ≤ y` in the target iff
`e.symm x ≤ e.symm y` in the source. The collection is equipped below with
lexicographic substitution and the resulting finite-set operad structure.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

namespace SetOperad

namespace AssocData

/-- The associative symmetric collection.

At a finite type `I`, `collection.obj` is `LinearOrder I`. For
`e : I ≃ J` extracted from the `Core FintypeCat` morphism, the map
sends `ord : LinearOrder I` to `e.symm.linearOrder` on `J`, so
`x ≤ y` in `J` iff `e.symm x ≤ e.symm y` in `I`. -/
noncomputable def collection : SymmetricCollection Type where
  obj X := LinearOrder X.of
  map {X Y} f :=
    TypeCat.ofHom fun ord =>
      let e : X.of ≃ Y.of := FinBijGroupoid.equivOfHom f
      letI : LinearOrder X.of := ord
      letI : DecidableEq Y.of := e.symm.decidableEq
      e.symm.linearOrder
  map_id X := by
    ext ord a b
    rfl
  map_comp {X Y Z} f g := by
    ext ord a b
    rfl

/-- The unit morphism for the associative collection.

It sends the unique element of the empty tensor `operadUnitSource` to the
canonical linear order on `PUnit`. -/
def unitMor : operadUnitSource (V := Type) ⟶ collection.eval arityOne :=
  TypeCat.ofHom fun _ : operadUnitSource (V := Type) =>
    (inferInstance : LinearOrder PUnit)

/-- Lexicographic substitution for the associative collection.

For `X : SubstitutionData`, an element of the source is an `Option`-indexed
family `fam` where `fam none` is the outer order on `X.index` and
`fam (some i)` is the inner order on `(X.obj i).of`. The map installs
`fam none` as `LinearOrder X.index` and `fam (some i)` as
`LinearOrder (X.obj i).of`, then returns the inferred Mathlib lexicographic
`LinearOrder` on the dependent sum `(a : X.index) × (X.obj a).of`. -/
noncomputable def substApp (X : SubstitutionData) :
    (substitutionSource collection).obj X ⟶ (substitutionTarget collection).obj X :=
  TypeCat.ofHom fun fam =>
    letI : LinearOrder X.index := fam none
    letI : (a : X.index) → LinearOrder (X.obj a).of := fun a => fam (some a)
    (inferInstance : LinearOrder (Σₗ a : X.index, (X.obj a).of))

private theorem substOuterOrder_eq (X Y : SubstitutionData) (f : X ⟶ Y)
    (fam : (substitutionSource collection).obj X) :
    ((substitutionSource collection).map f fam) none =
      let e : X.index ≃ Y.index := f.equiv
      letI : LinearOrder X.index := fam none
      letI : DecidableEq Y.index := e.symm.decidableEq
      e.symm.linearOrder := by
  have h := SetOperad.substitutionSource_map_apply_none collection f fam
  rw [h]
  rfl

private theorem substInnerOrder_eq (X Y : SubstitutionData) (f : X ⟶ Y)
    (fam : (substitutionSource collection).obj X) (i : X.index) :
    ((substitutionSource collection).map f fam) (some (f.equiv i)) =
      let eInner : (X.obj i).of ≃ (Y.obj (f.equiv i)).of :=
        FinBijGroupoid.equivOfHom (f.hom i)
      letI : LinearOrder (X.obj i).of := fam (some i)
      letI : DecidableEq (Y.obj (f.equiv i)).of := eInner.symm.decidableEq
      eInner.symm.linearOrder := by
  have h := SetOperad.substitutionSource_map_apply_some collection f fam i
  rw [h]
  rfl

private theorem substOuter_lt_iff (X Y : SubstitutionData) (f : X ⟶ Y)
    (fam : (substitutionSource collection).obj X) (a b : X.index) :
    let sourceOrder : LinearOrder X.index := fam none
    let targetOrder : LinearOrder Y.index :=
      ((substitutionSource collection).map f fam) none
    @LT.lt Y.index targetOrder.toLT (f.equiv a) (f.equiv b) ↔
      @LT.lt X.index sourceOrder.toLT a b := by
  change
    @LT.lt Y.index
        (((substitutionSource collection).map f fam) none).toLT
        (f.equiv a) (f.equiv b) ↔
      @LT.lt X.index (fam none).toLT a b
  have h_eq := substOuterOrder_eq X Y f fam
  rw [h_eq]
  let e : X.index ≃ Y.index := f.equiv
  let src : LinearOrder X.index := fam none
  let srcI : LinearOrder X.index := src
  have : DecidableEq X.index := srcI.toDecidableEq
  let decY : DecidableEq Y.index := e.symm.decidableEq
  let _srcI : LinearOrder X.index := src
  let _decY : DecidableEq Y.index := decY
  have h_toLT : (e.symm.linearOrder).toLT = e.symm.lt := rfl
  rw [h_toLT]
  have h_lt_def :
      @LT.lt Y.index e.symm.lt (e a) (e b) =
        @LT.lt X.index src.toLT (e.symm (e a)) (e.symm (e b)) :=
    rfl
  rw [h_lt_def]
  simp only [Equiv.symm_apply_apply]

private theorem substInner_le_iff (X Y : SubstitutionData) (f : X ⟶ Y)
    (fam : (substitutionSource collection).obj X) (i : X.index)
    (a b : (X.obj i).of) :
    let eInner : (X.obj i).of ≃ (Y.obj (f.equiv i)).of :=
      FinBijGroupoid.equivOfHom (f.hom i)
    let sourceOrder : LinearOrder (X.obj i).of := fam (some i)
    let targetOrder : LinearOrder (Y.obj (f.equiv i)).of :=
      ((substitutionSource collection).map f fam) (some (f.equiv i))
    @LE.le (Y.obj (f.equiv i)).of targetOrder.toLE (eInner a) (eInner b) ↔
      @LE.le (X.obj i).of sourceOrder.toLE a b := by
  change
    @LE.le (Y.obj (f.equiv i)).of
        (((substitutionSource collection).map f fam) (some (f.equiv i))).toLE
        ((FinBijGroupoid.equivOfHom (f.hom i) :
          (X.obj i).of ≃ (Y.obj (f.equiv i)).of) a)
        ((FinBijGroupoid.equivOfHom (f.hom i) :
          (X.obj i).of ≃ (Y.obj (f.equiv i)).of) b) ↔
      @LE.le (X.obj i).of (fam (some i)).toLE a b
  have h_eq := substInnerOrder_eq X Y f fam i
  rw [h_eq]
  let eInner : (X.obj i).of ≃ (Y.obj (f.equiv i)).of :=
    FinBijGroupoid.equivOfHom (f.hom i)
  let src : LinearOrder (X.obj i).of := fam (some i)
  let srcI : LinearOrder (X.obj i).of := src
  have : DecidableEq (X.obj i).of := srcI.toDecidableEq
  let decY : DecidableEq (Y.obj (f.equiv i)).of := eInner.symm.decidableEq
  let _srcI : LinearOrder (X.obj i).of := src
  let _decY : DecidableEq (Y.obj (f.equiv i)).of := decY
  have h_toLE : (eInner.symm.linearOrder).toLE = eInner.symm.le := rfl
  rw [h_toLE]
  have h_le_def :
      @LE.le (Y.obj (f.equiv i)).of eInner.symm.le (eInner a) (eInner b) =
        @LE.le (X.obj i).of src.toLE (eInner.symm (eInner a))
          (eInner.symm (eInner b)) :=
    rfl
  rw [h_le_def]
  simp only [Equiv.symm_apply_apply]

private theorem substLex_le_iff (X Y : SubstitutionData) (f : X ⟶ Y)
    (fam : (substitutionSource collection).obj X)
    (x y : (a : X.index) × (X.obj a).of) :
    let eInner := fun i => FinBijGroupoid.equivOfHom (f.hom i)
    let eTotal := Equiv.sigmaCongr f.equiv eInner
    let sourceOrder : LinearOrder ((a : X.index) × (X.obj a).of) :=
      substApp X fam
    let targetOrder : LinearOrder ((b : Y.index) × (Y.obj b).of) :=
      substApp Y ((substitutionSource collection).map f fam)
    @LE.le ((a : X.index) × (X.obj a).of) sourceOrder.toLE x y ↔
      @LE.le ((b : Y.index) × (Y.obj b).of) targetOrder.toLE
        (eTotal x) (eTotal y) := by
  rcases x with ⟨a1, b1⟩
  rcases y with ⟨a2, b2⟩
  change
    Sigma.Lex (fun a b => @LT.lt X.index (fam none).toLT a b)
      (fun i x y => @LE.le (X.obj i).of (fam (some i)).toLE x y)
      ⟨a1, b1⟩ ⟨a2, b2⟩ ↔
    Sigma.Lex
      (fun a b =>
        @LT.lt Y.index
          (((substitutionSource collection).map f fam) none).toLT a b)
      (fun j x y =>
        @LE.le (Y.obj j).of
          (((substitutionSource collection).map f fam) (some j)).toLE x y)
      ⟨f.equiv a1, (FinBijGroupoid.equivOfHom (f.hom a1)) b1⟩
      ⟨f.equiv a2, (FinBijGroupoid.equivOfHom (f.hom a2)) b2⟩
  rw [Sigma.lex_iff, Sigma.lex_iff]
  by_cases heq : a1 = a2
  · subst heq
    constructor
    · rintro (hOuter | ⟨_, hInner⟩)
      · exact Or.inl ((substOuter_lt_iff X Y f fam a1 a1).mpr hOuter)
      · exact Or.inr ⟨rfl, (substInner_le_iff X Y f fam a1 b1 b2).mpr hInner⟩
    · rintro (hOuter | ⟨_, hInner⟩)
      · exact Or.inl ((substOuter_lt_iff X Y f fam a1 a1).mp hOuter)
      · exact Or.inr ⟨rfl, (substInner_le_iff X Y f fam a1 b1 b2).mp hInner⟩
  · constructor
    · rintro (hOuter | ⟨heq', _⟩)
      · exact Or.inl ((substOuter_lt_iff X Y f fam a1 a2).mpr hOuter)
      · exact absurd heq' heq
    · rintro (hOuter | ⟨hEqT, _⟩)
      · exact Or.inl ((substOuter_lt_iff X Y f fam a1 a2).mp hOuter)
      · exact absurd (f.equiv.injective hEqT) heq

private theorem substTargetMap_eq (X Y : SubstitutionData) (f : X ⟶ Y)
    (ord : (substitutionTarget collection).obj X) :
    ((substitutionTarget collection).map f) ord =
      let eInner := fun i => FinBijGroupoid.equivOfHom (f.hom i)
      let eTotal : ((a : X.index) × (X.obj a).of) ≃
          ((b : Y.index) × (Y.obj b).of) :=
        Equiv.sigmaCongr f.equiv eInner
      letI : LinearOrder ((a : X.index) × (X.obj a).of) := ord
      letI : DecidableEq ((b : Y.index) × (Y.obj b).of) :=
        eTotal.symm.decidableEq
      eTotal.symm.linearOrder := by
  rfl

theorem subst_naturality {X Y : SubstitutionData} (f : X ⟶ Y) :
    (substitutionSource collection).map f ≫ substApp Y =
      substApp X ≫ (substitutionTarget collection).map f := by
  ext fam
  change
    substApp Y ((substitutionSource collection).map f fam) =
      ((substitutionTarget collection).map f) (substApp X fam)
  rw [substTargetMap_eq]
  let eInner := fun i => FinBijGroupoid.equivOfHom (f.hom i)
  let eTotal : ((a : X.index) × (X.obj a).of) ≃
      ((b : Y.index) × (Y.obj b).of) :=
    f.equiv.sigmaCongr eInner
  let sourceOrder : LinearOrder ((a : X.index) × (X.obj a).of) :=
    substApp X fam
  let targetOrder : LinearOrder ((b : Y.index) × (Y.obj b).of) :=
    substApp Y ((substitutionSource collection).map f fam)
  let _srcInst : LinearOrder ((a : X.index) × (X.obj a).of) := sourceOrder
  let _decInst : DecidableEq ((b : Y.index) × (Y.obj b).of) :=
    eTotal.symm.decidableEq
  change targetOrder = eTotal.symm.linearOrder
  apply LinearOrder.ext
  intro u v
  have hLex := substLex_le_iff X Y f fam (eTotal.symm u) (eTotal.symm v)
  dsimp only [eInner, eTotal] at hLex
  simp at hLex
  have hRfl :
      @LE.le ((a : X.index) × (X.obj a).of) sourceOrder.toLE
          (eTotal.symm u) (eTotal.symm v) ↔
        @LE.le ((b : Y.index) × (Y.obj b).of)
            (eTotal.symm.linearOrder).toLE u v := by
    rfl
  calc
    @LE.le ((b : Y.index) × (Y.obj b).of) targetOrder.toLE u v ↔
        @LE.le ((a : X.index) × (X.obj a).of) sourceOrder.toLE
          (eTotal.symm u) (eTotal.symm v) := hLex.symm
    _ ↔ @LE.le ((b : Y.index) × (Y.obj b).of)
          (eTotal.symm.linearOrder).toLE u v := hRfl

/-- Lexicographic substitution for the associative collection, natural under
bijections of the outer arity and all inner arities. -/
noncomputable def subst : substitutionSource collection ⟶ substitutionTarget collection where
  app := substApp
  naturality _ _ f := subst_naturality f

private theorem rightUnitInsert_apply_none (I : FintypeCat)
    (ord : collection.eval I) :
    rightUnitInsert collection unitMor I ord none = ord := by
  rfl

private theorem rightUnitInsert_apply_some (I : FintypeCat)
    (ord : collection.eval I) (i : I) :
    rightUnitInsert collection unitMor I ord (some i) =
      (inferInstance : LinearOrder PUnit) := by
  let c : Type := collection.eval I
  let f := UnitInsertion.rightFactorHom collection unitMor I
  let j : (UnitInsertion.rightTensorFamily c I).index := some i
  let a : FiniteFamily.typeTensorObj (FiniteFamily.singleton.obj c) :=
    (FiniteFamily.typeTensorSingletonEquiv c).symm ord
  let b : FiniteFamily.typeTensorObj
      (FiniteFamily.flatten.obj (UnitInsertion.rightNestedFamily c I)) :=
    FiniteFamily.typeTensorMap (UnitInsertion.rightSingletonToFlatten c I) a
  let t : FiniteFamily.typeTensorObj (UnitInsertion.rightTensorFamily c I) :=
    (FiniteFamily.typeTensorFlattenEquiv (UnitInsertion.rightNestedFamily c I)) b
  have h_eq : rightUnitInsert collection unitMor I =
      (FiniteFamily.typeTensorSingletonIso.inv.app c) ≫
      (FiniteFamily.typeTensor.map (UnitInsertion.rightSingletonToFlatten c I)) ≫
      (FiniteFamily.typeTensorFlattenIso.hom.app
        (UnitInsertion.rightNestedFamily c I)) ≫
      (FiniteFamily.typeTensor.map f) := by
    rfl
  change rightUnitInsert collection unitMor I ord (some i) =
    (inferInstance : LinearOrder PUnit)
  change rightUnitInsert collection unitMor I ord (f.equiv j) =
    (inferInstance : LinearOrder PUnit)
  rw [h_eq]
  change FiniteFamily.typeTensorMap f t (f.equiv j) =
    (inferInstance : LinearOrder PUnit)
  rw [FiniteFamily.typeTensorMap_apply]
  dsimp [f, j, UnitInsertion.rightFactorHom, unitMor]
  rfl

private theorem rightUnitInsert_apply (I : FintypeCat)
    (ord : collection.eval I) :
    rightUnitInsert collection unitMor I ord =
      fun o : Option I => match o with
        | none => ord
        | some _ => (inferInstance : LinearOrder PUnit) := by
  funext o
  cases o with
  | none => exact rightUnitInsert_apply_none I ord
  | some i => exact rightUnitInsert_apply_some I ord i

private theorem rightUnitRelabel_eq (I : FintypeCat)
    (ord : collection.eval I) :
    collection.relabelIso (rightUnitTotalIso I)
      (subst.app (rightUnitData I)
        (rightUnitInsert collection unitMor I ord)) = ord := by
  rw [rightUnitInsert_apply]
  apply LinearOrder.ext
  intro a b
  change @LE.le I
      (collection.relabelIso (rightUnitTotalIso I)
        (subst.app (rightUnitData I)
          (fun o : Option I => match o with
            | none => ord
            | some _ => (inferInstance : LinearOrder PUnit)))).toLE a b ↔
      @LE.le I ord.toLE a b
  change Sigma.Lex (fun x y => @LT.lt I ord.toLT x y)
      (fun _ (x1 : PUnit) (x2 : PUnit) =>
        @LE.le PUnit (inferInstance : LinearOrder PUnit).toLE x1 x2)
      ⟨a, PUnit.unit⟩ ⟨b, PUnit.unit⟩ ↔ @LE.le I ord.toLE a b
  rw [Sigma.lex_iff]
  constructor
  · rintro (hlt | ⟨heq, _⟩)
    · exact @le_of_lt I ord.toPreorder a b hlt
    · exact @le_of_eq I ord.toPartialOrder.toPreorder a b heq
  · intro hle
    by_cases heq : a = b
    · exact Or.inr ⟨heq, trivial⟩
    · exact Or.inl (@lt_of_le_of_ne I ord.toPartialOrder a b hle heq)

theorem isRightUnit : IsRightUnit collection unitMor subst := by
  intro I
  ext ord
  exact rightUnitRelabel_eq I ord

private theorem leftUnitInsert_apply_none (J : FintypeCat)
    (ord : collection.eval J) :
    leftUnitInsert collection unitMor J ord none =
      (inferInstance : LinearOrder PUnit) := by
  rfl

private theorem leftUnitInsert_apply_some (J : FintypeCat)
    (ord : collection.eval J) (p : PUnit) :
    leftUnitInsert collection unitMor J ord (some p) = ord := by
  rfl

private theorem leftUnitInsert_apply (J : FintypeCat)
    (ord : collection.eval J) :
    leftUnitInsert collection unitMor J ord =
      fun o : Option PUnit => match o with
        | none => (inferInstance : LinearOrder PUnit)
        | some _ => ord := by
  funext o
  cases o with
  | none => exact leftUnitInsert_apply_none J ord
  | some p => exact leftUnitInsert_apply_some J ord p

private theorem leftUnitRelabel_eq (J : FintypeCat)
    (ord : collection.eval J) :
    collection.relabelIso (leftUnitTotalIso J)
      (subst.app (leftUnitData J)
        (leftUnitInsert collection unitMor J ord)) = ord := by
  rw [leftUnitInsert_apply]
  apply LinearOrder.ext
  intro a b
  change @LE.le J
      (collection.relabelIso (leftUnitTotalIso J)
        (subst.app (leftUnitData J)
          (fun o : Option PUnit => match o with
            | none => (inferInstance : LinearOrder PUnit)
            | some _ => ord))).toLE a b ↔
      @LE.le J ord.toLE a b
  change Sigma.Lex
      (fun x y => @LT.lt PUnit (inferInstance : LinearOrder PUnit).toLT x y)
      (fun _ x y => @LE.le J ord.toLE x y)
      ⟨PUnit.unit, a⟩ ⟨PUnit.unit, b⟩ ↔ @LE.le J ord.toLE a b
  rw [Sigma.lex_iff]
  constructor
  · rintro (hlt | ⟨_, hle⟩)
    · exact False.elim (lt_irrefl _ hlt)
    · exact hle
  · intro hle
    exact Or.inr ⟨rfl, hle⟩

theorem isLeftUnit : IsLeftUnit collection unitMor subst := by
  intro J
  ext ord
  exact leftUnitRelabel_eq J ord

private theorem assocRouteA_apply
    (d : CategoryTheory.Operad.AssocData)
    (t : associativityCommonSource collection d) :
    associativityRouteA collection subst d t =
      subst.app d.outerAfterInnerData (fun o =>
        match o with
        | none => t ⟨none, PUnit.unit⟩
        | some i =>
          subst.app (d.localData i) (fun q =>
            match q with
            | none => t ⟨some i, none⟩
            | some j => t ⟨some i, some j⟩)) := by
  let X := AssocInsertion.groupingA collection d
  let tFlat :
      FiniteFamily.typeTensorObj
        ((FiniteFamily.map FiniteFamily.typeTensor).obj X) :=
    FiniteFamily.typeTensorFlattenEquiv X t
  have hFlat_none :
      tFlat none PUnit.unit = t ⟨none, PUnit.unit⟩ := by
    rfl
  have hFlat_some_none :
      ∀ (i : d.outer), tFlat (some i) none = t ⟨some i, none⟩ := by
    intro i
    rfl
  have hFlat_some_some :
      ∀ (i : d.outer) (j : d.middle i),
        tFlat (some i) (some j) = t ⟨some i, some j⟩ := by
    intro i j
    rfl
  have hFlat_some_eq :
      ∀ (i : d.outer),
        tFlat (some i) = fun q =>
          match q with
          | none => t ⟨some i, none⟩
          | some j => t ⟨some i, some j⟩ := by
    intro i
    funext q
    cases q with
    | none => exact hFlat_some_none i
    | some j => exact hFlat_some_some i j
  let fHom := AssocInsertion.groupingAToFactorsHom collection subst d
  let tMap := FiniteFamily.typeTensorMap fHom tFlat
  have hMap_none_eq :
      tMap none = fHom.hom none (tFlat none) := by
    have h := FiniteFamily.typeTensorMap_apply fHom tFlat none
    exact h
  have hMap_some_eq :
      ∀ (i : d.outer),
        tMap (some i) = fHom.hom (some i) (tFlat (some i)) := by
    intro i
    have h := FiniteFamily.typeTensorMap_apply fHom tFlat (some i)
    exact h
  have hHom_none :
      fHom.hom none =
        (FiniteTensor.singletonIso (V := Type)).hom.app
          (collection.eval d.outer) := by
    rfl
  have hHom_some :
      ∀ (i : d.outer),
        fHom.hom (some i) = subst.app (d.localData i) := by
    intro i
    rfl
  have hSingleton :
      ∀ (Y : Type)
        (g : FiniteFamily.typeTensorObj
          (FiniteFamily.singleton.obj Y)),
        (FiniteTensor.singletonIso (V := Type)).hom.app Y g =
          g PUnit.unit := by
    intro Y g
    change FiniteFamily.typeTensorSingletonEquiv Y g = g PUnit.unit
    rw [FiniteFamily.typeTensorSingletonEquiv_apply]
  have hMap_none : tMap none = t ⟨none, PUnit.unit⟩ := by
    have h1 : tMap none = fHom.hom none (tFlat none) := hMap_none_eq
    have h2 :
        fHom.hom none (tFlat none) =
          (FiniteTensor.singletonIso (V := Type)).hom.app
            (collection.eval d.outer) (tFlat none) := by
      exact congrArg (fun f => f (tFlat none)) hHom_none
    have h3 :
        (FiniteTensor.singletonIso (V := Type)).hom.app
            (collection.eval d.outer) (tFlat none) =
          tFlat none PUnit.unit := by
      exact hSingleton _ _
    exact (h1.trans (h2.trans (h3.trans hFlat_none)))
  have hMap_some :
      ∀ (i : d.outer),
        tMap (some i) =
          subst.app (d.localData i) (fun q =>
            match q with
            | none => t ⟨some i, none⟩
            | some j => t ⟨some i, some j⟩) := by
    intro i
    have h1 : tMap (some i) = fHom.hom (some i) (tFlat (some i)) :=
      hMap_some_eq i
    have h2 :
        fHom.hom (some i) (tFlat (some i)) =
          subst.app (d.localData i) (tFlat (some i)) := by
      exact congrArg (fun f => f (tFlat (some i))) (hHom_some i)
    have h3 :
        subst.app (d.localData i) (tFlat (some i)) =
          subst.app (d.localData i) (fun q =>
            match q with
            | none => t ⟨some i, none⟩
            | some j => t ⟨some i, some j⟩) := by
      exact congrArg (fun g => subst.app (d.localData i) g)
        (hFlat_some_eq i)
    exact h1.trans (h2.trans h3)
  have hMap_eq :
      tMap = fun o =>
        match o with
        | none => t ⟨none, PUnit.unit⟩
        | some i =>
          subst.app (d.localData i) (fun q =>
            match q with
            | none => t ⟨some i, none⟩
            | some j => t ⟨some i, some j⟩) := by
    funext o
    cases o with
    | none => exact hMap_none
    | some i => exact hMap_some i
  have hRoute :
      associativityRouteA collection subst d t =
        subst.app d.outerAfterInnerData tMap := by
    rfl
  have hFinal :
      subst.app d.outerAfterInnerData tMap =
        subst.app d.outerAfterInnerData (fun o =>
          match o with
          | none => t ⟨none, PUnit.unit⟩
          | some i =>
            subst.app (d.localData i) (fun q =>
              match q with
              | none => t ⟨some i, none⟩
              | some j => t ⟨some i, some j⟩)) := by
    exact congrArg (fun g => subst.app d.outerAfterInnerData g) hMap_eq
  exact hRoute.trans hFinal

private theorem assocRouteB_apply
    (d : CategoryTheory.Operad.AssocData)
    (t : associativityCommonSource collection d) :
    associativityRouteB collection subst d t =
      collection.relabelIso d.totalIso
        (subst.app d.innerData (fun o =>
          match o with
          | none =>
            subst.app d.middleData (fun q =>
              match q with
              | none => t ⟨none, PUnit.unit⟩
              | some i => t ⟨some i, none⟩)
          | some p => t ⟨some p.1, some p.2⟩)) := by
  let fAB := AssocInsertion.flattenAToFlattenBHom collection d
  let GB := AssocInsertion.groupingB collection d
  let tAfterAB := FiniteFamily.typeTensorMap fAB t
  have hAfterAB_none : tAfterAB ⟨none, none⟩ = t ⟨none, PUnit.unit⟩ := by
    have hMap := FiniteFamily.typeTensorMap_apply fAB t ⟨none, PUnit.unit⟩
    have hHom : fAB.hom ⟨none, PUnit.unit⟩ = 𝟙 _ := by rfl
    have h1 :
        tAfterAB (fAB.equiv ⟨none, PUnit.unit⟩) =
          fAB.hom ⟨none, PUnit.unit⟩ (t ⟨none, PUnit.unit⟩) := hMap
    have h2 :
        fAB.hom ⟨none, PUnit.unit⟩ (t ⟨none, PUnit.unit⟩) =
          t ⟨none, PUnit.unit⟩ := by
      rw [hHom]
      rfl
    have h3 :
        tAfterAB (fAB.equiv ⟨none, PUnit.unit⟩) = t ⟨none, PUnit.unit⟩ :=
      h1.trans h2
    have h4 :
        tAfterAB ⟨none, none⟩ = tAfterAB (fAB.equiv ⟨none, PUnit.unit⟩) := by
      rfl
    exact h4.trans h3
  have hAfterAB_some_none :
      ∀ (i : d.outer), tAfterAB ⟨none, some i⟩ = t ⟨some i, none⟩ := by
    intro i
    have hMap := FiniteFamily.typeTensorMap_apply fAB t ⟨some i, none⟩
    have hHom : fAB.hom ⟨some i, none⟩ = 𝟙 _ := by rfl
    have h1 :
        tAfterAB (fAB.equiv ⟨some i, none⟩) =
          fAB.hom ⟨some i, none⟩ (t ⟨some i, none⟩) := hMap
    have h2 :
        fAB.hom ⟨some i, none⟩ (t ⟨some i, none⟩) = t ⟨some i, none⟩ := by
      rw [hHom]
      rfl
    have h3 :
        tAfterAB (fAB.equiv ⟨some i, none⟩) = t ⟨some i, none⟩ := h1.trans h2
    have h4 :
        tAfterAB ⟨none, some i⟩ =
          tAfterAB (fAB.equiv ⟨some i, none⟩) := by
      rfl
    exact h4.trans h3
  have hAfterAB_some_some :
      ∀ (i : d.outer) (j : d.middle i),
        tAfterAB ⟨some ⟨i, j⟩, PUnit.unit⟩ = t ⟨some i, some j⟩ := by
    intro i j
    have hMap := FiniteFamily.typeTensorMap_apply fAB t ⟨some i, some j⟩
    have hHom : fAB.hom ⟨some i, some j⟩ = 𝟙 _ := by rfl
    have h1 :
        tAfterAB (fAB.equiv ⟨some i, some j⟩) =
          fAB.hom ⟨some i, some j⟩ (t ⟨some i, some j⟩) := hMap
    have h2 :
        fAB.hom ⟨some i, some j⟩ (t ⟨some i, some j⟩) =
          t ⟨some i, some j⟩ := by
      rw [hHom]
      rfl
    have h3 :
        tAfterAB (fAB.equiv ⟨some i, some j⟩) = t ⟨some i, some j⟩ :=
      h1.trans h2
    have h4 :
        tAfterAB ⟨some ⟨i, j⟩, PUnit.unit⟩ =
          tAfterAB (fAB.equiv ⟨some i, some j⟩) := by
      rfl
    exact h4.trans h3
  let tCurried := FiniteFamily.typeTensorFlattenEquiv GB tAfterAB
  have hCurried_none_none : tCurried none none = t ⟨none, PUnit.unit⟩ := by
    have hFlat : tCurried none none = tAfterAB ⟨none, none⟩ := by rfl
    exact hFlat.trans hAfterAB_none
  have hCurried_none_some :
      ∀ (i : d.outer), tCurried none (some i) = t ⟨some i, none⟩ := by
    intro i
    have hFlat : tCurried none (some i) = tAfterAB ⟨none, some i⟩ := by rfl
    exact hFlat.trans (hAfterAB_some_none i)
  have hCurried_some :
      ∀ (i : d.outer) (j : d.middle i),
        tCurried (some ⟨i, j⟩) PUnit.unit = t ⟨some i, some j⟩ := by
    intro i j
    have hFlat :
        tCurried (some ⟨i, j⟩) PUnit.unit =
          tAfterAB ⟨some ⟨i, j⟩, PUnit.unit⟩ := by
      rfl
    exact hFlat.trans (hAfterAB_some_some i j)
  have hCurried_none_eq :
      tCurried none = fun q =>
        match q with
        | none => t ⟨none, PUnit.unit⟩
        | some i => t ⟨some i, none⟩ := by
    funext q
    cases q with
    | none => exact hCurried_none_none
    | some i => exact hCurried_none_some i
  have hCurried_some_pointwise :
      ∀ (p : (substitutionTotalObj d.middleData : Type)),
        tCurried (some p) PUnit.unit = t ⟨some p.1, some p.2⟩ := by
    intro p
    rcases p with ⟨i, j⟩
    exact hCurried_some i j
  let fB := AssocInsertion.groupingBToFactorsHom collection subst d
  let tMap := FiniteFamily.typeTensorMap fB tCurried
  have hMap_none_eq : tMap none = fB.hom none (tCurried none) := by
    have h := FiniteFamily.typeTensorMap_apply fB tCurried none
    exact h
  have hMap_some_eq :
      ∀ (p : (substitutionTotalObj d.middleData : Type)),
        tMap (some p) = fB.hom (some p) (tCurried (some p)) := by
    intro p
    have h := FiniteFamily.typeTensorMap_apply fB tCurried (some p)
    exact h
  have hHom_none : fB.hom none = subst.app d.middleData := by rfl
  have hHom_some :
      ∀ (p : (substitutionTotalObj d.middleData : Type)),
        fB.hom (some p) =
          (FiniteTensor.singletonIso (V := Type)).hom.app
            (collection.eval (d.inner p)) := by
    intro p
    rfl
  have hSingleton :
      ∀ (Y : Type)
        (g : FiniteFamily.typeTensorObj (FiniteFamily.singleton.obj Y)),
        (FiniteTensor.singletonIso (V := Type)).hom.app Y g = g PUnit.unit := by
    intro Y g
    change FiniteFamily.typeTensorSingletonEquiv Y g = g PUnit.unit
    rw [FiniteFamily.typeTensorSingletonEquiv_apply]
  have hMap_none :
      tMap none =
        subst.app d.middleData (fun q =>
          match q with
          | none => t ⟨none, PUnit.unit⟩
          | some i => t ⟨some i, none⟩) := by
    have h1 : tMap none = fB.hom none (tCurried none) := hMap_none_eq
    have h2 :
        fB.hom none (tCurried none) =
          subst.app d.middleData (tCurried none) := by
      exact congrArg (fun f => f (tCurried none)) hHom_none
    have h3 :
        subst.app d.middleData (tCurried none) =
          subst.app d.middleData (fun q =>
            match q with
            | none => t ⟨none, PUnit.unit⟩
            | some i => t ⟨some i, none⟩) := by
      exact congrArg (fun g => subst.app d.middleData g) hCurried_none_eq
    exact (h1.trans h2).trans h3
  have hMap_some :
      ∀ (p : (substitutionTotalObj d.middleData : Type)),
        tMap (some p) = t ⟨some p.1, some p.2⟩ := by
    intro p
    have h1 : tMap (some p) = fB.hom (some p) (tCurried (some p)) :=
      hMap_some_eq p
    have h2 :
        fB.hom (some p) (tCurried (some p)) =
          (FiniteTensor.singletonIso (V := Type)).hom.app
            (collection.eval (d.inner p)) (tCurried (some p)) := by
      exact congrArg (fun f => f (tCurried (some p))) (hHom_some p)
    have h3 :
        (FiniteTensor.singletonIso (V := Type)).hom.app
            (collection.eval (d.inner p)) (tCurried (some p)) =
          tCurried (some p) PUnit.unit := by
      exact hSingleton _ _
    have h4 : tCurried (some p) PUnit.unit = t ⟨some p.1, some p.2⟩ :=
      hCurried_some_pointwise p
    exact (h1.trans (h2.trans h3)).trans h4
  have hMap_eq :
      tMap = fun o =>
        match o with
        | none =>
          subst.app d.middleData (fun q =>
            match q with
            | none => t ⟨none, PUnit.unit⟩
            | some i => t ⟨some i, none⟩)
        | some p => t ⟨some p.1, some p.2⟩ := by
    funext o
    cases o with
    | none => exact hMap_none
    | some p => exact hMap_some p
  have hRoute :
      associativityRouteB collection subst d t =
        collection.relabelIso d.totalIso (subst.app d.innerData tMap) := by
    rfl
  have hFinal :
      collection.relabelIso d.totalIso (subst.app d.innerData tMap) =
        collection.relabelIso d.totalIso
          (subst.app d.innerData (fun o =>
            match o with
            | none =>
              subst.app d.middleData (fun q =>
                match q with
                | none => t ⟨none, PUnit.unit⟩
                | some i => t ⟨some i, none⟩)
            | some p => t ⟨some p.1, some p.2⟩)) := by
    exact congrArg
      (fun g => collection.relabelIso d.totalIso (subst.app d.innerData g)) hMap_eq
  exact hRoute.trans hFinal

private theorem sigmaAssoc_lex_iff {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}
    (rα : α → α → Prop) (rβ : ∀ a, β a → β a → Prop)
    (rγ : ∀ a b, γ a b → γ a b → Prop)
    (x y : (ab : Σ a : α, β a) × γ ab.1 ab.2) :
    Sigma.Lex (Sigma.Lex rα rβ) (fun ab => rγ ab.1 ab.2) x y ↔
      Sigma.Lex rα (fun a => Sigma.Lex (rβ a) (rγ a))
        (Equiv.sigmaAssoc γ x) (Equiv.sigmaAssoc γ y) := by
  rcases x with ⟨⟨a₁, b₁⟩, c₁⟩
  rcases y with ⟨⟨a₂, b₂⟩, c₂⟩
  constructor
  · intro h
    cases h with
    | left _ _ h₁ =>
      cases h₁ with
      | left _ _ hα => exact Sigma.Lex.left _ _ hα
      | right _ _ hβ => exact Sigma.Lex.right _ _ (Sigma.Lex.left _ _ hβ)
    | right _ _ hγ => exact Sigma.Lex.right _ _ (Sigma.Lex.right _ _ hγ)
  · intro h
    cases h with
    | left _ _ hα => exact Sigma.Lex.left _ _ (Sigma.Lex.left _ _ hα)
    | right _ _ h₂ =>
      cases h₂ with
      | left _ _ hβ => exact Sigma.Lex.left _ _ (Sigma.Lex.right _ _ hβ)
      | right _ _ hγ => exact Sigma.Lex.right _ _ hγ

private theorem assocRelabel_eq (d : CategoryTheory.Operad.AssocData)
    (t : associativityCommonSource collection d) :
    subst.app d.outerAfterInnerData (fun o =>
      match o with
      | none => t ⟨none, PUnit.unit⟩
      | some i =>
        subst.app (d.localData i) (fun q =>
          match q with
          | none => t ⟨some i, none⟩
          | some j => t ⟨some i, some j⟩)) =
    collection.relabelIso d.totalIso
      (subst.app d.innerData (fun o =>
        match o with
        | none =>
          subst.app d.middleData (fun q =>
            match q with
            | none => t ⟨none, PUnit.unit⟩
            | some i => t ⟨some i, none⟩)
        | some p => t ⟨some p.1, some p.2⟩)) := by
  apply LinearOrder.ext
  intro a b
  change
    Sigma.Lex (fun x y => @LT.lt d.outer (t ⟨none, PUnit.unit⟩).toLT x y)
      (fun i x y =>
        Sigma.Lex (fun x y => @LT.lt _ (t ⟨some i, none⟩).toLT x y)
          (fun j x y => @LE.le _ (t ⟨some i, some j⟩).toLE x y) x y) a b ↔
    @LE.le _
      (collection.relabelIso d.totalIso
        (subst.app d.innerData (fun o =>
          match o with
          | none =>
            subst.app d.middleData (fun q =>
              match q with
              | none => t ⟨none, PUnit.unit⟩
              | some i => t ⟨some i, none⟩)
          | some p => t ⟨some p.1, some p.2⟩))).toLE a b
  change
    Sigma.Lex (fun x y => @LT.lt d.outer (t ⟨none, PUnit.unit⟩).toLT x y)
      (fun i x y =>
        Sigma.Lex (fun x y => @LT.lt _ (t ⟨some i, none⟩).toLT x y)
          (fun j x y => @LE.le _ (t ⟨some i, some j⟩).toLE x y) x y) a b ↔
    Sigma.Lex
      (Sigma.Lex (fun x y => @LT.lt d.outer (t ⟨none, PUnit.unit⟩).toLT x y)
        (fun i x y => @LT.lt _ (t ⟨some i, none⟩).toLT x y))
      (fun ab x y => @LE.le _ (t ⟨some ab.1, some ab.2⟩).toLE x y)
      ((Equiv.sigmaAssoc (fun i j => (d.inner ⟨i, j⟩ : Type))).symm a)
      ((Equiv.sigmaAssoc (fun i j => (d.inner ⟨i, j⟩ : Type))).symm b)
  have h := sigmaAssoc_lex_iff
    (rα := fun x y => @LT.lt d.outer (t ⟨none, PUnit.unit⟩).toLT x y)
    (rβ := fun i x y => @LT.lt _ (t ⟨some i, none⟩).toLT x y)
    (rγ := fun i j x y => @LE.le _ (t ⟨some i, some j⟩).toLE x y)
    ((Equiv.sigmaAssoc (fun i j => (d.inner ⟨i, j⟩ : Type))).symm a)
    ((Equiv.sigmaAssoc (fun i j => (d.inner ⟨i, j⟩ : Type))).symm b)
  simp at h
  exact h.symm

theorem isAssociative : IsAssociative collection subst := by
  intro d
  ext t
  change
    associativityRouteA collection subst d t =
      associativityRouteB collection subst d t
  rw [assocRouteA_apply, assocRouteB_apply]
  exact assocRelabel_eq d t

end AssocData

/-- The associative set operad of linear orders with lexicographic substitution. -/
noncomputable def assoc : SetOperad where
  toCollection := AssocData.collection
  unit := AssocData.unitMor
  subst := AssocData.subst
  right_unit := AssocData.isRightUnit
  left_unit := AssocData.isLeftUnit
  assoc := AssocData.isAssociative

end SetOperad

end CategoryTheory.Operad
