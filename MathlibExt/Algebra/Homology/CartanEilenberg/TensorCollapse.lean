/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorTorResolution
import MathlibExt.Algebra.Homology.Homotopy
import MathlibExt.Algebra.Homology.HomotopyRetract
import MathlibExt.Algebra.Homology.Functor
import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The Cartan–Eilenberg vertical-homology tensor comparison

Let R be commutative, K,L nonnegative R-module complexes and P a Cartan–Eilenberg resolution of
L. For each inner total degree q, the canonical homogeneous tensor pairing from the finite
Tor-resolution complex to vertical homology of the tensor convolution is an isomorphism.

The displayed isomorphism is oriented from vertical homology to the Tor-resolution complex, so
its inverse is this canonical pairing. No degreewise flatness hypothesis on K is required for
this comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {L : ChainComplex (ModuleCat.{u} R) ℕ}

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance : HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- Let R be commutative, L a nonnegative R-module complex, P a Cartan–Eilenberg resolution and a ∈
ℕ. The row homology complex has term H_j(P.bicomplex.Xₐ) in each original degree j and zero
differential. -/
private noncomputable abbrev rowHomologyComplex
    (P : CartanEilenbergResolution L) (a : ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ where
  X j := (P.bicomplex.X a).homology j
  d _ _ := 0

private noncomputable abbrev rowProjectionComponent
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    (P.bicomplex.X a).X j ⟶ (rowHomologyComplex P a).X j := by
  cases j with
  | zero =>
      exact P.rowHomologyZeroProjection a ≫ (P.rowHomologyZeroIso a).inv
  | succ j =>
      exact (P.termComponentSplitting a (j + 1)).r ≫
        (P.cyclesComponentShortComplex a (j + 1)).g ≫
        (P.cartanEilenbergRowHomologySuccIso a j).inv

private noncomputable abbrev rowRepresentativeComponent
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    (rowHomologyComplex P a).X j ⟶ (P.bicomplex.X a).X j := by
  cases j with
  | zero =>
      exact (P.rowHomologyZeroIso a).hom ≫
        biprod.desc
          ((P.cyclesComponentSplitting a 0).s ≫
            (P.termComponentShortComplex a 0).f)
          (P.termComponentSplitting a 0).s
  | succ j =>
      exact (P.cartanEilenbergRowHomologySuccIso a j).hom ≫
        (P.cyclesComponentSplitting a (j + 1)).s ≫
        (P.termComponentShortComplex a (j + 1)).f

@[simp]
private theorem rowProjectionComponent_zero
    (P : CartanEilenbergResolution L) (a : ℕ) :
    rowProjectionComponent P a 0 =
      P.rowHomologyZeroProjection a ≫ (P.rowHomologyZeroIso a).inv :=
  rfl

@[simp]
private theorem rowProjectionComponent_succ
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    rowProjectionComponent P a (j + 1) =
      (P.termComponentSplitting a (j + 1)).r ≫
        (P.cyclesComponentShortComplex a (j + 1)).g ≫
        (P.cartanEilenbergRowHomologySuccIso a j).inv :=
  rfl

@[simp]
private theorem rowRepresentativeComponent_zero
    (P : CartanEilenbergResolution L) (a : ℕ) :
    rowRepresentativeComponent P a 0 =
      (P.rowHomologyZeroIso a).hom ≫
        biprod.desc
          ((P.cyclesComponentSplitting a 0).s ≫
            (P.termComponentShortComplex a 0).f)
          (P.termComponentSplitting a 0).s :=
  rfl

@[simp]
private theorem rowRepresentativeComponent_succ
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    rowRepresentativeComponent P a (j + 1) =
      (P.cartanEilenbergRowHomologySuccIso a j).hom ≫
        (P.cyclesComponentSplitting a (j + 1)).s ≫
        (P.termComponentShortComplex a (j + 1)).f :=
  rfl

private theorem rowComponent_retract_zero
    (P : CartanEilenbergResolution L) (a : ℕ) :
    ((P.rowHomologyZeroIso a).hom ≫
        biprod.desc
          ((P.cyclesComponentSplitting a 0).s ≫
            (P.termComponentShortComplex a 0).f)
          (P.termComponentSplitting a 0).s) ≫
      (P.rowHomologyZeroProjection a ≫ (P.rowHomologyZeroIso a).inv) =
      𝟙 ((P.bicomplex.X a).homology 0) := by
  let c := P.cyclesComponentSplitting a 0
  let t := P.termComponentSplitting a 0
  have hmid :
      biprod.desc
          ((P.cyclesComponentSplitting a 0).s ≫
            (P.termComponentShortComplex a 0).f)
          (P.termComponentSplitting a 0).s ≫
        P.rowHomologyZeroProjection a =
      𝟙 ((P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a) := by
    have h := (ShortComplex.Splitting.compLeft c t).s_g
    convert h using 1 <;> rfl
  calc
    ((P.rowHomologyZeroIso a).hom ≫
          biprod.desc
            ((P.cyclesComponentSplitting a 0).s ≫
              (P.termComponentShortComplex a 0).f)
            (P.termComponentSplitting a 0).s) ≫
        (P.rowHomologyZeroProjection a ≫
          (P.rowHomologyZeroIso a).inv) =
      (P.rowHomologyZeroIso a).hom ≫
        (biprod.desc
            ((P.cyclesComponentSplitting a 0).s ≫
              (P.termComponentShortComplex a 0).f)
            (P.termComponentSplitting a 0).s ≫
          P.rowHomologyZeroProjection a) ≫
        (P.rowHomologyZeroIso a).inv := by simp only [Category.assoc]
    _ = (P.rowHomologyZeroIso a).hom ≫ 𝟙 _ ≫
        (P.rowHomologyZeroIso a).inv := by
      exact congrArg
        (fun k => (P.rowHomologyZeroIso a).hom ≫ k ≫
          (P.rowHomologyZeroIso a).inv) hmid
    _ = 𝟙 _ := by simp

private theorem rowComponent_retract_succ
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    ((P.cartanEilenbergRowHomologySuccIso a j).hom ≫
        (P.cyclesComponentSplitting a (j + 1)).s ≫
        (P.termComponentShortComplex a (j + 1)).f) ≫
      ((P.termComponentSplitting a (j + 1)).r ≫
        (P.cyclesComponentShortComplex a (j + 1)).g ≫
        (P.cartanEilenbergRowHomologySuccIso a j).inv) =
      𝟙 ((P.bicomplex.X a).homology (j + 1)) := by
  let e := P.cartanEilenbergRowHomologySuccIso a j
  let c := P.cyclesComponentSplitting a (j + 1)
  let t := P.termComponentSplitting a (j + 1)
  have hfr :
      (P.termComponentShortComplex a (j + 1)).f ≫ t.r =
        𝟙 (P.cyclesComponentShortComplex a (j + 1)).X₂ := by
    exact t.f_r
  have hsg :
      c.s ≫ (P.cyclesComponentShortComplex a (j + 1)).g =
        𝟙 ((P.homologyResolution (j + 1)).complex.X a) := by
    exact c.s_g
  have hpref :
      ((e.hom ≫ c.s ≫ (P.termComponentShortComplex a (j + 1)).f) ≫ t.r) =
        (e.hom ≫ c.s) ≫ 𝟙 (P.cyclesComponentShortComplex a (j + 1)).X₂ := by
    calc
      _ = (e.hom ≫ c.s) ≫
          ((P.termComponentShortComplex a (j + 1)).f ≫ t.r) := by
        simp only [Category.assoc]
      _ = _ := by rw [hfr]
  have hid₁ :
      (e.hom ≫ c.s) ≫ 𝟙 (P.cyclesComponentShortComplex a (j + 1)).X₂ =
        e.hom ≫ c.s := Category.comp_id _
  have hcycles :
      (e.hom ≫ c.s) ≫
          (P.cyclesComponentShortComplex a (j + 1)).g =
        e.hom ≫ 𝟙 ((P.homologyResolution (j + 1)).complex.X a) := by
    calc
      _ = e.hom ≫
          (c.s ≫ (P.cyclesComponentShortComplex a (j + 1)).g) := by
        rw [Category.assoc]
      _ = _ := by rw [hsg]
  have hid₂ :
      e.hom ≫ 𝟙 ((P.homologyResolution (j + 1)).complex.X a) = e.hom :=
    Category.comp_id _
  let suffix := (P.cyclesComponentShortComplex a (j + 1)).g ≫ e.inv
  have hprefPost := congrArg (fun k => k ≫ suffix) hpref
  have hid₁Post := congrArg (fun k => k ≫ suffix) hid₁
  have hcyclesPost := congrArg (fun k => k ≫ e.inv) hcycles
  have hid₂Post := congrArg (fun k => k ≫ e.inv) hid₂
  calc
    _ = ((e.hom ≫ c.s ≫
          (P.termComponentShortComplex a (j + 1)).f) ≫ t.r) ≫ suffix :=
      (Category.assoc _ _ suffix).symm
    _ = ((e.hom ≫ c.s) ≫
          𝟙 (P.cyclesComponentShortComplex a (j + 1)).X₂) ≫ suffix :=
      hprefPost
    _ = (e.hom ≫ c.s) ≫ suffix := hid₁Post
    _ = ((e.hom ≫ c.s) ≫
          (P.cyclesComponentShortComplex a (j + 1)).g) ≫ e.inv :=
      Category.assoc _ _ _
    _ = (e.hom ≫
          𝟙 ((P.homologyResolution (j + 1)).complex.X a)) ≫ e.inv :=
      hcyclesPost
    _ = e.hom ≫ e.inv := hid₂Post
    _ = 𝟙 _ := e.hom_inv_id

private noncomputable def rowProjection
    (P : CartanEilenbergResolution L) (a : ℕ) :
    P.bicomplex.X a ⟶ rowHomologyComplex P a where
  f := rowProjectionComponent P a
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [show (rowHomologyComplex P a).d (j + 1) j = 0 from rfl, comp_zero]
    rw [P.bicomplex_d₂ a j]
    symm
    change (P.termComponentShortComplex a (j + 1)).g ≫
      (P.cyclesComponentShortComplex a j).f ≫
      (P.termComponentShortComplex a j).f ≫
      rowProjectionComponent P a j = 0
    cases j with
    | zero =>
        rw [rowProjectionComponent_zero]
        rw [P.termComponent_f_comp_rowHomologyZeroProjection_assoc]
        slice_lhs 2 3 =>
          rw [(P.cyclesComponentShortComplex a 0).zero]
        simp
    | succ j =>
        rw [rowProjectionComponent_succ]
        rw [(P.termComponentSplitting a (j + 1)).f_r_assoc]
        rw [(P.cyclesComponentShortComplex a (j + 1)).zero_assoc]
        simp

private theorem iCycles_comp_rowProjection_f
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    (P.bicomplex.X a).iCycles j ≫ (rowProjection P a).f j =
      (P.bicomplex.X a).homologyπ j := by
  cases j with
  | zero =>
      let C := P.bicomplex.X a
      let eO := C.opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
        (P.rowHomologyZeroRightData a).opcyclesIso
      have hIso : (P.rowHomologyZeroIso a).hom =
          C.homologyι 0 ≫ eO.hom := by
        change (C.homologyIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
            (P.rowHomologyZeroRightData a).homologyIso.hom = _
        calc
          _ = (C.homologyIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
              ((P.rowHomologyZeroRightData a).homologyIso.hom ≫
                (P.rowHomologyZeroRightData a).ι) := by
            change _ = _ ≫ (_ ≫ 𝟙 _)
            simp
          _ = (C.homologyIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
              ((C.sc' 1 0 0).homologyι ≫
                (P.rowHomologyZeroRightData a).opcyclesIso.hom) := by
            rw [(P.rowHomologyZeroRightData a).homologyIso_hom_comp_ι]
          _ = ((C.homologyIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
              (C.sc' 1 0 0).homologyι) ≫
                (P.rowHomologyZeroRightData a).opcyclesIso.hom := by
            simp only [Category.assoc]
          _ = (C.homologyι 0 ≫
              (C.opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom) ≫
                (P.rowHomologyZeroRightData a).opcyclesIso.hom := by
            rw [HomologicalComplex.homologyIsoSc'_hom_ι]
          _ = _ := Category.assoc _ _ _
      let p₀ : C.X 0 ⟶
          (P.homologyResolution 0).complex.X a ⊞
            (P.boundaryResolution 0).complex.X a := by
        exact P.rowHomologyZeroProjection a
      have hProj : C.pOpcycles 0 ≫ eO.hom = p₀ := by
        change C.pOpcycles 0 ≫
            ((C.opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
              (P.rowHomologyZeroRightData a).opcyclesIso.hom) =
          P.rowHomologyZeroProjection a
        convert P.rowHomologyZero_pOpcycles_comp_explicitQuotient a using 1
      have hrow : (rowProjection P a).f 0 =
          p₀ ≫ (P.rowHomologyZeroIso a).inv := rfl
      rw [hrow]
      calc
        C.iCycles 0 ≫ (p₀ ≫ (P.rowHomologyZeroIso a).inv) =
            (C.iCycles 0 ≫ p₀) ≫ (P.rowHomologyZeroIso a).inv :=
          (Category.assoc _ _ _).symm
        _ = (C.iCycles 0 ≫ (C.pOpcycles 0 ≫ eO.hom)) ≫
            (P.rowHomologyZeroIso a).inv :=
          congrArg (fun k => (C.iCycles 0 ≫ k) ≫
            (P.rowHomologyZeroIso a).inv) hProj.symm
        _ = ((C.iCycles 0 ≫ C.pOpcycles 0) ≫ eO.hom) ≫
            (P.rowHomologyZeroIso a).inv := by
          rw [Category.assoc]
        _ = ((C.homologyπ 0 ≫ C.homologyι 0) ≫ eO.hom) ≫
            (P.rowHomologyZeroIso a).inv :=
          congrArg (fun k => (k ≫ eO.hom) ≫
            (P.rowHomologyZeroIso a).inv) (C.homology_π_ι (i := 0)).symm
        _ = (C.homologyπ 0 ≫ (C.homologyι 0 ≫ eO.hom)) ≫
            (P.rowHomologyZeroIso a).inv := by
          rw [Category.assoc]
        _ = (C.homologyπ 0 ≫ (P.rowHomologyZeroIso a).hom) ≫
            (P.rowHomologyZeroIso a).inv :=
          congrArg (fun k => (C.homologyπ 0 ≫ k) ≫
            (P.rowHomologyZeroIso a).inv) hIso.symm
        _ = C.homologyπ 0 := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  | succ r =>
      let C := P.bicomplex.X a
      let eS := C.cyclesIsoSc' (r + 2) (r + 1) r (by simp) (by simp)
      let eL : (C.sc' (r + 2) (r + 1) r).cycles ≅
          (P.cyclesResolution (r + 1)).complex.X a := by
        exact (P.cartanEilenbergRowHomologySuccLeftData a r).cyclesIso
      let eC : C.cycles (r + 1) ≅
          (P.cyclesResolution (r + 1)).complex.X a := eS ≪≫ eL
      have heC : eC.hom =
          (P.cartanEilenbergRowCyclesSuccIso a r).hom := rfl
      have hEL : eL.hom ≫ (P.termComponentShortComplex a (r + 1)).f =
          (C.sc' (r + 2) (r + 1) r).iCycles := by
        exact (P.cartanEilenbergRowHomologySuccLeftData a r).cyclesIso_hom_comp_i
      have hELpost := congrArg (fun k => eS.hom ≫ k) hEL
      have hEnd : eS.hom ≫ (C.sc' (r + 2) (r + 1) r).iCycles =
          C.iCycles (r + 1) :=
        HomologicalComplex.cyclesIsoSc'_hom_iCycles C
          (r + 2) (r + 1) r (by simp) (by simp)
      have hInc : eC.hom ≫ (P.termComponentShortComplex a (r + 1)).f =
          C.iCycles (r + 1) := by
        dsimp only [eC, Iso.trans_hom]
        exact (Category.assoc _ _ _).trans (hELpost.trans hEnd)
      let rmap : C.X (r + 1) ⟶
          (P.termComponentShortComplex a (r + 1)).X₁ := by
        exact (P.termComponentSplitting a (r + 1)).r
      let rpPost : C.X (r + 1) ⟶
          (P.homologyResolution (r + 1)).complex.X a := by
        exact rmap ≫
          (P.cyclesComponentShortComplex a (r + 1)).g
      let rp : C.X (r + 1) ⟶ C.homology (r + 1) :=
        rpPost ≫ (P.cartanEilenbergRowHomologySuccIso a r).inv
      have hrow : (rowProjection P a).f (r + 1) = rp := rfl
      have hrp : rp ≫ (P.cartanEilenbergRowHomologySuccIso a r).hom =
          rpPost := by
        dsimp only [rp]
        calc
          (rpPost ≫ (P.cartanEilenbergRowHomologySuccIso a r).inv) ≫
              (P.cartanEilenbergRowHomologySuccIso a r).hom =
            rpPost ≫ ((P.cartanEilenbergRowHomologySuccIso a r).inv ≫
              (P.cartanEilenbergRowHomologySuccIso a r).hom) :=
            Category.assoc _ _ _
          _ = rpPost ≫ 𝟙 _ := congrArg (fun k => rpPost ≫ k)
            (P.cartanEilenbergRowHomologySuccIso a r).inv_hom_id
          _ = rpPost := Category.comp_id _
      have hfr : (P.termComponentShortComplex a (r + 1)).f ≫ rmap = 𝟙 _ := by
        exact (P.termComponentSplitting a (r + 1)).f_r
      have hfp : (P.termComponentShortComplex a (r + 1)).f ≫ rpPost =
          (P.cyclesComponentShortComplex a (r + 1)).g := by
        dsimp only [rpPost]
        calc
          (P.termComponentShortComplex a (r + 1)).f ≫
              (rmap ≫ (P.cyclesComponentShortComplex a (r + 1)).g) =
            ((P.termComponentShortComplex a (r + 1)).f ≫ rmap) ≫
              (P.cyclesComponentShortComplex a (r + 1)).g :=
            (Category.assoc _ _ _).symm
          _ = 𝟙 _ ≫ (P.cyclesComponentShortComplex a (r + 1)).g :=
            congrArg (fun k => k ≫
              (P.cyclesComponentShortComplex a (r + 1)).g) hfr
          _ = _ := Category.id_comp _
      have hleft : C.iCycles (r + 1) ≫ rpPost =
          eC.hom ≫ (P.cyclesComponentShortComplex a (r + 1)).g := by
        calc
          C.iCycles (r + 1) ≫ rpPost =
              (eC.hom ≫ (P.termComponentShortComplex a (r + 1)).f) ≫
                rpPost := congrArg (fun k => k ≫ rpPost) hInc.symm
          _ = eC.hom ≫
              ((P.termComponentShortComplex a (r + 1)).f ≫ rpPost) :=
            Category.assoc _ _ _
          _ = eC.hom ≫ (P.cyclesComponentShortComplex a (r + 1)).g :=
            congrArg (fun k => eC.hom ≫ k) hfp
      have hright : C.homologyπ (r + 1) ≫
          (P.cartanEilenbergRowHomologySuccIso a r).hom =
          eC.hom ≫ (P.cyclesComponentShortComplex a (r + 1)).g := by
        rw [P.homologyπ_comp_cartanEilenbergRowHomologySuccIso_hom]
        rw [← heC]
        rfl
      have hpost : (C.iCycles (r + 1) ≫ rp) ≫
            (P.cartanEilenbergRowHomologySuccIso a r).hom =
          C.homologyπ (r + 1) ≫
            (P.cartanEilenbergRowHomologySuccIso a r).hom := by
        calc
          _ = C.iCycles (r + 1) ≫
              (rp ≫ (P.cartanEilenbergRowHomologySuccIso a r).hom) :=
            Category.assoc _ _ _
          _ = C.iCycles (r + 1) ≫ rpPost :=
            congrArg (fun k => C.iCycles (r + 1) ≫ k) hrp
          _ = eC.hom ≫ (P.cyclesComponentShortComplex a (r + 1)).g := hleft
          _ = _ := hright.symm
      rw [hrow]
      exact (cancel_mono (P.cartanEilenbergRowHomologySuccIso a r).hom).mp hpost

private noncomputable def rowRepresentative
    (P : CartanEilenbergResolution L) (a : ℕ) :
    rowHomologyComplex P a ⟶ P.bicomplex.X a where
  f := rowRepresentativeComponent P a
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [show (rowHomologyComplex P a).d (j + 1) j = 0 from rfl, zero_comp]
    rw [P.bicomplex_d₂ a j]
    rw [rowRepresentativeComponent_succ]
    change ((P.cartanEilenbergRowHomologySuccIso a j).hom ≫
      (P.cyclesComponentSplitting a (j + 1)).s ≫
      (P.termComponentShortComplex a (j + 1)).f) ≫
        (P.termDifferential j).f a = 0
    change ((P.cartanEilenbergRowHomologySuccIso a j).hom ≫
      (P.cyclesComponentSplitting a (j + 1)).s ≫
      (P.termComponentShortComplex a (j + 1)).f) ≫
        ((P.termComponentShortComplex a (j + 1)).g ≫
          (P.cyclesComponentShortComplex a j).f ≫
          (P.termComponentShortComplex a j).f) = 0
    simp only [Category.assoc]
    rw [(P.termComponentShortComplex a (j + 1)).zero_assoc]
    simp

private theorem rowRepresentative_comp_projection
    (P : CartanEilenbergResolution L) (a : ℕ) :
    rowRepresentative P a ≫ rowProjection P a =
      𝟙 (rowHomologyComplex P a) := by
  apply HomologicalComplex.Hom.ext
  funext j
  cases j with
  | zero =>
      dsimp only [rowRepresentative, rowProjection,
        HomologicalComplex.comp_f, HomologicalComplex.id_f]
      rw [rowRepresentativeComponent_zero, rowProjectionComponent_zero]
      exact rowComponent_retract_zero P a
  | succ j =>
      dsimp only [rowRepresentative, rowProjection,
        HomologicalComplex.comp_f, HomologicalComplex.id_f]
      rw [rowRepresentativeComponent_succ, rowProjectionComponent_succ]
      exact rowComponent_retract_succ P a j

private noncomputable def rowContractingComponent
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    (P.bicomplex.X a).X j ⟶ (P.bicomplex.X a).X (j + 1) :=
  (P.termComponentSplitting a j).r ≫
    (P.cyclesComponentSplitting a j).r ≫
    (P.termComponentSplitting a (j + 1)).s

private noncomputable def rowContractingHom
    (P : CartanEilenbergResolution L) (a : ℕ)
    (i j : ℕ) : (P.bicomplex.X a).X i ⟶ (P.bicomplex.X a).X j :=
  if h : j = i + 1 then by
    subst j
    exact rowContractingComponent P a i
  else 0

private theorem rowContractingHom_succ
    (P : CartanEilenbergResolution L) (a i : ℕ) :
    rowContractingHom P a i (i + 1) = rowContractingComponent P a i := by
  simp [rowContractingHom]
  rfl

private theorem rowContractingHom_zero_of_ne
    (P : CartanEilenbergResolution L) (a i j : ℕ) (h : j ≠ i + 1) :
    rowContractingHom P a i j = 0 := by
  simp [rowContractingHom, h]
  rfl

private theorem rowProjectionRepresentative_zero
    (P : CartanEilenbergResolution L) (a : ℕ) :
    (rowProjection P a ≫ rowRepresentative P a).f 0 =
      P.rowHomologyZeroProjection a ≫
        biprod.desc
          ((P.cyclesComponentSplitting a 0).s ≫
            (P.termComponentShortComplex a 0).f)
          (P.termComponentSplitting a 0).s := by
  dsimp only [HomologicalComplex.comp_f, rowProjection, rowRepresentative]
  rw [rowProjectionComponent_zero, rowRepresentativeComponent_zero]
  let e := P.rowHomologyZeroIso a
  let s := biprod.desc
    ((P.cyclesComponentSplitting a 0).s ≫
      (P.termComponentShortComplex a 0).f)
    (P.termComponentSplitting a 0).s
  have h := e.inv_hom_id_assoc s
  calc
    (P.rowHomologyZeroProjection a ≫ e.inv) ≫ (e.hom ≫ s) =
        P.rowHomologyZeroProjection a ≫ (e.inv ≫ e.hom ≫ s) := by
      simp only [Category.assoc]
    _ = P.rowHomologyZeroProjection a ≫ s :=
      congrArg (fun k => P.rowHomologyZeroProjection a ≫ k) h

private theorem rowProjectionRepresentative_succ
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    (rowProjection P a ≫ rowRepresentative P a).f (j + 1) =
      (P.termComponentSplitting a (j + 1)).r ≫
        (P.cyclesComponentShortComplex a (j + 1)).g ≫
        (P.cyclesComponentSplitting a (j + 1)).s ≫
        (P.termComponentShortComplex a (j + 1)).f := by
  dsimp only [HomologicalComplex.comp_f, rowProjection, rowRepresentative]
  rw [rowProjectionComponent_succ, rowRepresentativeComponent_succ]
  let p := (P.termComponentSplitting a (j + 1)).r ≫
    (P.cyclesComponentShortComplex a (j + 1)).g
  let e := P.cartanEilenbergRowHomologySuccIso a j
  let s := (P.cyclesComponentSplitting a (j + 1)).s ≫
    (P.termComponentShortComplex a (j + 1)).f
  have h := e.inv_hom_id_assoc s
  calc
    (p ≫ e.inv) ≫ (e.hom ≫ s) = p ≫ (e.inv ≫ e.hom ≫ s) := by
      simp only [Category.assoc]
    _ = p ≫ s := congrArg (fun k => p ≫ k) h

private theorem rowContracting_zero_comp_d
    (P : CartanEilenbergResolution L) (a : ℕ) :
    rowContractingComponent P a 0 ≫ (P.bicomplex.X a).d 1 0 =
      (ShortComplex.Splitting.compLeft
        (P.cyclesComponentSplitting a 0)
        (P.termComponentSplitting a 0)).r ≫
      ((P.cyclesComponentShortComplex a 0).f ≫
        (P.termComponentShortComplex a 0).f) := by
  rw [P.bicomplex_d₂]
  change ((P.termComponentSplitting a 0).r ≫
      (P.cyclesComponentSplitting a 0).r ≫
      (P.termComponentSplitting a 1).s) ≫
    ((P.termComponentShortComplex a 1).g ≫
      (P.cyclesComponentShortComplex a 0).f ≫
      (P.termComponentShortComplex a 0).f) = _
  rw [ShortComplex.Splitting.compLeft_r]
  simp only [Category.assoc]
  rw [(P.termComponentSplitting a 1).s_g_assoc]

private theorem rowContraction_zero_identity
    (P : CartanEilenbergResolution L) (a : ℕ) :
    𝟙 ((P.bicomplex.X a).X 0) =
      rowContractingComponent P a 0 ≫ (P.bicomplex.X a).d 1 0 +
        (rowProjection P a ≫ rowRepresentative P a).f 0 := by
  rw [rowContracting_zero_comp_d, rowProjectionRepresentative_zero]
  exact (ShortComplex.Splitting.compLeft
    (P.cyclesComponentSplitting a 0)
    (P.termComponentSplitting a 0)).id.symm

private theorem rowContraction_succ_identity
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    𝟙 ((P.bicomplex.X a).X (j + 1)) =
      (P.bicomplex.X a).d (j + 1) j ≫ rowContractingComponent P a j +
        rowContractingComponent P a (j + 1) ≫
          (P.bicomplex.X a).d (j + 2) (j + 1) +
        (rowProjection P a ≫ rowRepresentative P a).f (j + 1) := by
  rw [rowProjectionRepresentative_succ]
  rw [P.bicomplex_d₂ a j, P.bicomplex_d₂ a (j + 1)]
  change 𝟙 _ =
    ((P.termComponentShortComplex a (j + 1)).g ≫
      (P.cyclesComponentShortComplex a j).f ≫
      (P.termComponentShortComplex a j).f) ≫
        ((P.termComponentSplitting a j).r ≫
          (P.cyclesComponentSplitting a j).r ≫
          (P.termComponentSplitting a (j + 1)).s) +
    ((P.termComponentSplitting a (j + 1)).r ≫
      (P.cyclesComponentSplitting a (j + 1)).r ≫
      (P.termComponentSplitting a (j + 2)).s) ≫
        ((P.termComponentShortComplex a (j + 2)).g ≫
          (P.cyclesComponentShortComplex a (j + 1)).f ≫
          (P.termComponentShortComplex a (j + 1)).f) +
    (P.termComponentSplitting a (j + 1)).r ≫
      (P.cyclesComponentShortComplex a (j + 1)).g ≫
      (P.cyclesComponentSplitting a (j + 1)).s ≫
      (P.termComponentShortComplex a (j + 1)).f
  simp only [Category.assoc]
  rw [(P.termComponentSplitting a j).f_r_assoc]
  rw [(P.cyclesComponentSplitting a j).f_r_assoc]
  rw [(P.termComponentSplitting a (j + 2)).s_g_assoc]
  have hc := (P.cyclesComponentSplitting a (j + 1)).id
  have hc' :
      (P.cyclesComponentSplitting a (j + 1)).r ≫
          (P.cyclesComponentShortComplex a (j + 1)).f +
        (P.cyclesComponentShortComplex a (j + 1)).g ≫
          (P.cyclesComponentSplitting a (j + 1)).s =
      𝟙 (P.termComponentShortComplex a (j + 1)).X₁ := by
    exact hc
  have ht := (P.termComponentSplitting a (j + 1)).id
  rw [← ht]
  have hcw' :
      (P.termComponentSplitting a (j + 1)).r ≫
          (P.cyclesComponentSplitting a (j + 1)).r ≫
          (P.cyclesComponentShortComplex a (j + 1)).f ≫
          (P.termComponentShortComplex a (j + 1)).f +
        (P.termComponentSplitting a (j + 1)).r ≫
          (P.cyclesComponentShortComplex a (j + 1)).g ≫
          (P.cyclesComponentSplitting a (j + 1)).s ≫
          (P.termComponentShortComplex a (j + 1)).f =
      (P.termComponentSplitting a (j + 1)).r ≫
        (P.termComponentShortComplex a (j + 1)).f := by
    calc
      _ = (P.termComponentSplitting a (j + 1)).r ≫
          ((P.cyclesComponentSplitting a (j + 1)).r ≫
              (P.cyclesComponentShortComplex a (j + 1)).f +
            (P.cyclesComponentShortComplex a (j + 1)).g ≫
              (P.cyclesComponentSplitting a (j + 1)).s) ≫
          (P.termComponentShortComplex a (j + 1)).f := by
        simp only [Preadditive.comp_add, Preadditive.add_comp,
          Category.assoc]
      _ = (P.termComponentSplitting a (j + 1)).r ≫ 𝟙 _ ≫
          (P.termComponentShortComplex a (j + 1)).f := by rw [hc']
      _ = _ := by rw [Category.id_comp]
  calc
    (P.termComponentSplitting a (j + 1)).r ≫
          (P.termComponentShortComplex a (j + 1)).f +
        (P.termComponentShortComplex a (j + 1)).g ≫
          (P.termComponentSplitting a (j + 1)).s =
      (P.termComponentShortComplex a (j + 1)).g ≫
          (P.termComponentSplitting a (j + 1)).s +
        (P.termComponentSplitting a (j + 1)).r ≫
          (P.termComponentShortComplex a (j + 1)).f := add_comm _ _
    _ = (P.termComponentShortComplex a (j + 1)).g ≫
          (P.termComponentSplitting a (j + 1)).s +
        ((P.termComponentSplitting a (j + 1)).r ≫
            (P.cyclesComponentSplitting a (j + 1)).r ≫
            (P.cyclesComponentShortComplex a (j + 1)).f ≫
            (P.termComponentShortComplex a (j + 1)).f +
          (P.termComponentSplitting a (j + 1)).r ≫
            (P.cyclesComponentShortComplex a (j + 1)).g ≫
            (P.cyclesComponentSplitting a (j + 1)).s ≫
            (P.termComponentShortComplex a (j + 1)).f) :=
      congrArg
        (fun k => (P.termComponentShortComplex a (j + 1)).g ≫
          (P.termComponentSplitting a (j + 1)).s + k) hcw'.symm
    _ = _ := (add_assoc _ _ _).symm

private noncomputable def rowContractionHomotopy
    (P : CartanEilenbergResolution L) (a : ℕ) :
    Homotopy (𝟙 (P.bicomplex.X a))
      (rowProjection P a ≫ rowRepresentative P a) where
  hom := rowContractingHom P a
  zero i j hij := by
    apply rowContractingHom_zero_of_ne
    intro h
    apply hij
    simp [h]
  comm i := by
    cases i with
    | zero =>
        rw [_root_.dNext_eq_zero _ _ (by simp)]
        rw [_root_.prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
        rw [rowContractingHom_succ]
        simp only [HomologicalComplex.id_f, zero_add]
        exact rowContraction_zero_identity P a
    | succ j =>
        rw [_root_.dNext_eq _
          (show (ComplexShape.down ℕ).Rel (j + 1) j by simp)]
        rw [_root_.prevD_eq _
          (show (ComplexShape.down ℕ).Rel (j + 2) (j + 1) by simp)]
        rw [rowContractingHom_succ, rowContractingHom_succ]
        simp only [HomologicalComplex.id_f]
        exact rowContraction_succ_identity P a j

private noncomputable def rowHomotopyEquiv
    (P : CartanEilenbergResolution L) (a : ℕ) :
    HomotopyEquiv (P.bicomplex.X a) (rowHomologyComplex P a) :=
  (HomotopyEquiv.ofRetract
    (rowRepresentative P a) (rowProjection P a)
    (rowRepresentative_comp_projection P a)
    (rowContractionHomotopy P a).symm).symm

private noncomputable def tensorRowHomotopyEquiv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a : ℕ) :
    HomotopyEquiv (tensorObj K (P.bicomplex.X a))
      (tensorObj K (rowHomologyComplex P a)) := by
  let e := rowHomotopyEquiv P a
  refine
    { hom := tensorHom (𝟙 K) e.hom
      inv := tensorHom (𝟙 K) e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · exact (Homotopy.ofEq (by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.comp_id])).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 K) e.homotopyHomInvId
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ)).trans
            (Homotopy.ofEq (tensorHom_id_id K (P.bicomplex.X a))))
  · exact (Homotopy.ofEq (by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.comp_id])).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 K) e.homotopyInvHomId
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ)).trans
            (Homotopy.ofEq (tensorHom_id_id K (rowHomologyComplex P a))))

private noncomputable def tensorRowHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (tensorObj K (P.bicomplex.X a)).homology q ≅
      (tensorObj K (rowHomologyComplex P a)).homology q :=
  (tensorRowHomotopyEquiv K P a).toHomologyIso q

private noncomputable def actualRowPairingComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      (tensorObj K (P.bicomplex.X a)).homology q := by
  change K.homology ij.val.1 ⊗ (P.bicomplex.X a).homology ij.val.2 ⟶
    (tensorObj K (P.bicomplex.X a)).homology q
  exact ChainGradedPairing.pairHomology
      (𝟙 (tensorObj K (P.bicomplex.X a)))
      (ChainGradedPairing.homologyDescentData
        (𝟙 (tensorObj K (P.bicomplex.X a))))
      ij.val.1 ij.val.2 ≫
    (homologyIsoOfEq (tensorObj K (P.bicomplex.X a))
      (Finset.mem_antidiagonal.mp ij.property)).hom

private structure KunnethEvaluationData
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) where
  iso : (kunnethTorResolutionComplex K P q).X a ≅
    ⨁ fun ij : KunnethAntidiagonal q =>
      (kunnethTorResolutionSummand K P ij).X a
  pairing_component : ∀ ij : KunnethAntidiagonal q,
    biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          (kunnethTorResolutionSummand K P ij).X a) ij ≫
      iso.inv ≫ (kunnethCEVerticalHomologyPairing K P q).f a =
        actualRowPairingComponent K P a q ij

private noncomputable def kunnethEvaluationData
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    KunnethEvaluationData K P a q := by
  let e := (HomologicalComplex.eval (ModuleCat.{u} R)
    (ComplexShape.down ℕ) a).mapBiproduct
      (fun ij : KunnethAntidiagonal q => kunnethTorResolutionSummand K P ij)
  refine { iso := ?_, pairing_component := ?_ }
  · unfold kunnethTorResolutionComplex
    exact e
  · intro ij
    let inj : (kunnethTorResolutionSummand K P ij).X a ⟶
        (kunnethTorResolutionComplex K P q).X a := by
      unfold kunnethTorResolutionComplex
      exact (biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          kunnethTorResolutionSummand K P ij) ij).f a
    have hEval : biproduct.ι
          (fun ij : KunnethAntidiagonal q =>
            (kunnethTorResolutionSummand K P ij).X a) ij ≫ e.inv = inj := by
      unfold inj
      rw [Functor.mapBiproduct_inv, biproduct.ι_desc]
      rfl
    have hPair : inj ≫ (kunnethCEVerticalHomologyPairing K P q).f a =
        actualRowPairingComponent K P a q ij := by
      unfold inj
      exact kunnethCEVerticalHomologyPairing_ι_f K P q a ij
    have hEvalPost := congrArg (fun k => k ≫
      (kunnethCEVerticalHomologyPairing K P q).f a) hEval
    exact Eq.trans (Category.assoc _ _ _).symm (Eq.trans hEvalPost hPair)

private noncomputable abbrev kunnethEvaluationIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :=
  (kunnethEvaluationData K P a q).iso

private noncomputable def zeroRowPairingComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      (tensorObj K (rowHomologyComplex P a)).homology q := by
  change K.homology ij.val.1 ⊗
      (P.bicomplex.X a).homology ij.val.2 ⟶
    (tensorObj K (rowHomologyComplex P a)).homology q
  exact
    (𝟙 (K.homology ij.val.1) ⊗ₘ
      ((rowHomotopyEquiv P a).toHomologyIso ij.val.2).hom) ≫
      ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K (rowHomologyComplex P a)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (rowHomologyComplex P a))))
        ij.val.1 ij.val.2 ≫
      (homologyIsoOfEq (tensorObj K (rowHomologyComplex P a))
        (Finset.mem_antidiagonal.mp ij.property)).hom

private noncomputable def zeroRowPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (kunnethTorResolutionComplex K P q).X a ⟶
      (tensorObj K (rowHomologyComplex P a)).homology q :=
  (kunnethEvaluationIso K P a q).hom ≫
    biproduct.desc (zeroRowPairingComponent K P a q)

@[reassoc]
private theorem actualRowPairingComponent_comp_tensorRowHomologyIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    actualRowPairingComponent K P a q ij ≫
        (tensorRowHomologyIso K P a q).hom =
      zeroRowPairingComponent K P a q ij := by
  let C := P.bicomplex.X a
  let Q := rowHomologyComplex P a
  let g := rowProjection P a
  let PC : ChainGradedPairing K C (tensorObj K C) := 𝟙 _
  let PQ : ChainGradedPairing K Q (tensorObj K Q) := 𝟙 _
  let tg := tensorHom (𝟙 K) g
  have hpair : ∀ i j,
      PC.pair i j ≫ tg.f (i + j) =
        (𝟙 (K.X i) ⊗ₘ g.f j) ≫ PQ.pair i j := by
    intro i j
    exact (ChainGradedPairing.pair_naturality PC PQ
      (𝟙 K) g tg (by simp [PC, PQ, tg]) i j).symm
  have hnat := ChainGradedPairing.pairHomology_naturality
    PC (ChainGradedPairing.homologyDescentData PC)
    PQ (ChainGradedPairing.homologyDescentData PQ)
    (𝟙 K) g tg hpair ij.val.1 ij.val.2
  unfold actualRowPairingComponent zeroRowPairingComponent
  change
    (ChainGradedPairing.pairHomology PC
          (ChainGradedPairing.homologyDescentData PC)
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K C)
          (Finset.mem_antidiagonal.mp ij.property)).hom) ≫
      homologyMap tg q =
    (𝟙 (K.homology ij.val.1) ⊗ₘ homologyMap g ij.val.2) ≫
      ChainGradedPairing.pairHomology PQ
        (ChainGradedPairing.homologyDescentData PQ)
        ij.val.1 ij.val.2 ≫
      (homologyIsoOfEq (tensorObj K Q)
        (Finset.mem_antidiagonal.mp ij.property)).hom
  slice_lhs 2 3 =>
    rw [← homologyIsoOfEq_hom_naturality tg
      (Finset.mem_antidiagonal.mp ij.property)]
  rw [← Category.assoc, hnat.symm]
  simp only [homologyMap_id, Category.assoc]
  dsimp only [Q]

private noncomputable def tensorObjXIsoBiproduct
    (K Q : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (tensorObj K Q).X n ≅
      ⨁ fun ij : KunnethAntidiagonal n => K.X ij.val.1 ⊗ Q.X ij.val.2 := by
  let A : KunnethAntidiagonal n → ModuleCat.{u} R := fun ij =>
    K.X ij.val.1 ⊗ Q.X ij.val.2
  let fwd : (tensorObj K Q).X n ⟶ ⨁ A :=
    mapBifunctorDesc fun i j (h : i + j = n) =>
      biproduct.ι A
        (⟨(i, j), Finset.mem_antidiagonal.mpr h⟩ : KunnethAntidiagonal n)
  let bwd : (⨁ A) ⟶ (tensorObj K Q).X n :=
    biproduct.desc fun ij : KunnethAntidiagonal n =>
      ιTensorObj K Q ij.val.1 ij.val.2 n
        (Finset.mem_antidiagonal.mp ij.property)
  refine
    { hom := fwd
      inv := bwd
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply mapBifunctor.hom_ext
    intro i j h
    dsimp only [fwd, bwd]
    rw [ι_mapBifunctorDesc_assoc]
    rw [biproduct.ι_desc]
    rfl
  · apply biproduct.hom_ext'
    intro ij
    dsimp only [fwd, bwd]
    rw [biproduct.ι_desc_assoc]
    rw [ι_mapBifunctorDesc]
    rfl

private theorem ιTensorObj_comp_tensorObjXIsoBiproduct_hom
    (K Q : ChainComplex (ModuleCat.{u} R) ℕ)
    (i j n : ℕ) (h : i + j = n) :
    ιTensorObj K Q i j n h ≫ (tensorObjXIsoBiproduct K Q n).hom =
      biproduct.ι
        (fun ij : KunnethAntidiagonal n => K.X ij.val.1 ⊗ Q.X ij.val.2)
        (⟨(i, j), Finset.mem_antidiagonal.mpr h⟩ : KunnethAntidiagonal n) := by
  unfold tensorObjXIsoBiproduct
  rw [ι_mapBifunctorDesc]

private theorem biproduct_ι_comp_tensorObjXIsoBiproduct_inv
    (K Q : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ) (ij : KunnethAntidiagonal n) :
    biproduct.ι
        (fun ij : KunnethAntidiagonal n => K.X ij.val.1 ⊗ Q.X ij.val.2) ij ≫
      (tensorObjXIsoBiproduct K Q n).inv =
    ιTensorObj K Q ij.val.1 ij.val.2 n
      (Finset.mem_antidiagonal.mp ij.property) := by
  unfold tensorObjXIsoBiproduct
  rw [biproduct.ι_desc]

private noncomputable abbrev tensorRowPiece
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down' (1 : ℕ)) :=
  ((tensorRight ((rowHomologyComplex P a).X j)).mapHomologicalComplex
    (ComplexShape.down' (1 : ℕ))).obj K

private abbrev shiftedTensorEmbedding (j : ℕ) :=
  ComplexShape.embeddingDown'Add (A := ℕ) 1 j

private noncomputable abbrev shiftedTensorRowPiece
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a j : ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (tensorRowPiece K P a j).extend (shiftedTensorEmbedding j)

private noncomputable abbrev finiteShiftedTensorComplex
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ⨁ fun j : Fin (q + 2) => shiftedTensorRowPiece K P a j.val

private theorem shiftedTensorEmbedding_f (i j : ℕ) :
    (shiftedTensorEmbedding j).f i = i + j := by
  dsimp [shiftedTensorEmbedding, ComplexShape.embeddingDown'Add,
    ComplexShape.Embedding.mk']

private noncomputable abbrev shiftedTensorRowPieceXIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j n : ℕ) (h : i + j = n) :
    (shiftedTensorRowPiece K P a j).X n ≅
      K.X i ⊗ (rowHomologyComplex P a).X j :=
  (tensorRowPiece K P a j).extendXIso (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f i j).trans h)

private noncomputable abbrev shiftedTensorForwardComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (i j : ℕ) (h : i + j = n) :
    K.X i ⊗ (rowHomologyComplex P a).X j ⟶
      ⨁ fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n := by
  let jf : Fin (q + 2) := ⟨j, by omega⟩
  exact (shiftedTensorRowPieceXIso K P a i j n h).inv ≫
      biproduct.ι
        (fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n) jf

private theorem shiftedTensorForwardComponent_eq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (i j : ℕ) (h : i + j = n) :
    shiftedTensorForwardComponent K P a q n hn i j h =
      (shiftedTensorRowPieceXIso K P a i j n h).inv ≫
        biproduct.ι
          (fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n)
          (⟨j, by omega⟩ : Fin (q + 2)) := by
  rfl

private noncomputable abbrev shiftedTensorBackwardComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (jf : Fin (q + 2)) :
    (shiftedTensorRowPiece K P a jf.val).X n ⟶
      (tensorObj K (rowHomologyComplex P a)).X n := by
  by_cases hle : jf.val ≤ n
  · exact (shiftedTensorRowPieceXIso K P a (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle)).hom ≫
      ιTensorObj K (rowHomologyComplex P a) (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle)
  · exact 0

private theorem shiftedTensorBackwardComponent_eq_of_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (jf : Fin (q + 2))
    (hle : jf.val ≤ n) :
    shiftedTensorBackwardComponent K P a q n jf =
      (shiftedTensorRowPieceXIso K P a (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle)).hom ≫
      ιTensorObj K (rowHomologyComplex P a) (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle) := by
  unfold shiftedTensorBackwardComponent
  split_ifs
  rfl

private theorem shiftedTensorBackwardComponent_eq_of_not_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (jf : Fin (q + 2))
    (hle : ¬ jf.val ≤ n) :
    shiftedTensorBackwardComponent K P a q n jf = 0 := by
  unfold shiftedTensorBackwardComponent
  split_ifs
  rfl

private theorem shiftedTensorBackwardComponent_eq_with
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (jf : Fin (q + 2))
    (i : ℕ) (h : i + jf.val = n) :
    shiftedTensorBackwardComponent K P a q n jf =
      (shiftedTensorRowPieceXIso K P a i jf.val n h).hom ≫
      ιTensorObj K (rowHomologyComplex P a) i jf.val n h := by
  have hle : jf.val ≤ n := by
    calc
      jf.val ≤ i + jf.val := Nat.le_add_left jf.val i
      _ = n := h
  rw [shiftedTensorBackwardComponent_eq_of_le (hle := hle)]
  have hi : n - jf.val = i := by omega
  subst i
  rfl

private noncomputable def tensorShiftedBaseIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1) :
    (tensorObj K (rowHomologyComplex P a)).X n ≅
      ⨁ fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).X n := by
  let Q := rowHomologyComplex P a
  let J := Fin (q + 2)
  let X : J → ModuleCat.{u} R := fun jf =>
    (shiftedTensorRowPiece K P a jf.val).X n
  let fwdComponent (i j : ℕ) (h : i + j = n) :
      K.X i ⊗ Q.X j ⟶ ⨁ X :=
    shiftedTensorForwardComponent K P a q n hn i j h
  let fwd₀ : (tensorObj K Q).X n ⟶ ⨁ X :=
    mapBifunctorDesc fwdComponent
  let bwdComponent (jf : J) : X jf ⟶ (tensorObj K Q).X n :=
    shiftedTensorBackwardComponent K P a q n jf
  let bwd₀ : (⨁ X) ⟶ (tensorObj K Q).X n :=
    biproduct.desc bwdComponent
  have hsource : fwd₀ ≫ bwd₀ = 𝟙 ((tensorObj K Q).X n) := by
    apply mapBifunctor.hom_ext
    intro i j h
    change i + j = n at h
    rw [ι_mapBifunctorDesc_assoc]
    dsimp only [fwdComponent]
    rw [shiftedTensorForwardComponent_eq]
    erw [Category.assoc, biproduct.ι_desc]
    dsimp only [bwdComponent]
    rw [shiftedTensorBackwardComponent_eq_with (i := i) (h := h)]
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
    rfl
  have hbase : bwd₀ ≫ fwd₀ = 𝟙 (⨁ X) := by
    apply biproduct.hom_ext'
    intro jf
    rw [biproduct.ι_desc_assoc]
    dsimp only [bwdComponent]
    by_cases hle : jf.val ≤ n
    · let i := n - jf.val
      let h : i + jf.val = n := Nat.sub_add_cancel hle
      rw [shiftedTensorBackwardComponent_eq_with
        (i := i) (h := h)]
      erw [Category.assoc, ι_mapBifunctorDesc]
      dsimp only [fwdComponent]
      rw [shiftedTensorForwardComponent_eq]
      erw [Iso.hom_inv_id_assoc]
      rfl
    · rw [shiftedTensorBackwardComponent_eq_of_not_le (hle := hle)]
      have hz : IsZero (X jf) := by
        apply (tensorRowPiece K P a jf.val).isZero_extend_X
        intro i
        change i + jf.val ≠ n
        omega
      exact hz.eq_of_src _ _
  let baseIso : (tensorObj K Q).X n ≅ ⨁ X :=
    { hom := fwd₀
      inv := bwd₀
      hom_inv_id := hsource
      inv_hom_id := hbase }
  exact baseIso

private theorem ιTensorObj_comp_tensorShiftedBaseIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (i j : ℕ) (h : i + j = n) :
    ιTensorObj K (rowHomologyComplex P a) i j n h ≫
        (tensorShiftedBaseIso K P a q n hn).hom =
      shiftedTensorForwardComponent K P a q n hn i j h := by
  unfold tensorShiftedBaseIso
  rw [ι_mapBifunctorDesc]

private theorem biproduct_ι_comp_tensorShiftedBaseIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (jf : Fin (q + 2)) :
    biproduct.ι
        (fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n) jf ≫
        (tensorShiftedBaseIso K P a q n hn).inv =
      shiftedTensorBackwardComponent K P a q n jf := by
  unfold tensorShiftedBaseIso
  rw [biproduct.ι_desc]

private theorem biproduct_ι_comp_evalMapBiproduct_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ)
    (jf : Fin (q + 2)) :
    biproduct.ι
        (fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n) jf ≫
        ((HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) n).mapBiproduct
            (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)).inv =
      (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf).f n := by
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc]
  rfl

private theorem biproduct_ι_f_comp_evalMapBiproduct_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ)
    (jf : Fin (q + 2)) :
    (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf).f n ≫
        ((HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) n).mapBiproduct
            (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)).hom =
      biproduct.ι
        (fun jf : Fin (q + 2) => (shiftedTensorRowPiece K P a jf.val).X n) jf := by
  rw [← cancel_mono ((HomologicalComplex.eval (ModuleCat.{u} R)
    (ComplexShape.down ℕ) n).mapBiproduct
      (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [biproduct_ι_comp_evalMapBiproduct_inv]

private noncomputable def tensorShiftedXIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1) :
    (tensorObj K (rowHomologyComplex P a)).X n ≅
      (finiteShiftedTensorComplex K P a q).X n :=
  tensorShiftedBaseIso K P a q n hn ≪≫
    ((HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.down ℕ) n).mapBiproduct
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)).symm

private theorem ιTensorObj_comp_tensorShiftedXIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (i j : ℕ) (h : i + j = n) :
    ιTensorObj K (rowHomologyComplex P a) i j n h ≫
        (tensorShiftedXIso K P a q n hn).hom =
      (shiftedTensorRowPieceXIso K P a i j n h).inv ≫
        (biproduct.ι
          (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)
          (⟨j, by omega⟩ : Fin (q + 2))).f n := by
  rw [tensorShiftedXIso, Iso.trans_hom, ← Category.assoc,
    ιTensorObj_comp_tensorShiftedBaseIso_hom]
  erw [shiftedTensorForwardComponent_eq]
  erw [Category.assoc, biproduct_ι_comp_evalMapBiproduct_inv]

private theorem biproduct_ι_f_comp_tensorShiftedXIso_inv_of_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (jf : Fin (q + 2)) (hle : jf.val ≤ n) :
    (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf).f n ≫
        (tensorShiftedXIso K P a q n hn).inv =
      (shiftedTensorRowPieceXIso K P a (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle)).hom ≫
      ιTensorObj K (rowHomologyComplex P a) (n - jf.val) jf.val n
        (Nat.sub_add_cancel hle) := by
  erw [tensorShiftedXIso, Iso.trans_inv, Iso.symm_inv, ← Category.assoc,
    biproduct_ι_f_comp_evalMapBiproduct_hom,
    biproduct_ι_comp_tensorShiftedBaseIso_inv]
  erw [shiftedTensorBackwardComponent_eq_of_le (hle := hle)]

private theorem biproduct_ι_f_comp_tensorShiftedXIso_inv_of_eq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (jf : Fin (q + 2)) (i : ℕ) (h : i + jf.val = n) :
    (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf).f n ≫
        (tensorShiftedXIso K P a q n hn).inv =
      (shiftedTensorRowPieceXIso K P a i jf.val n h).hom ≫
      ιTensorObj K (rowHomologyComplex P a) i jf.val n h := by
  have hle : jf.val ≤ n := by
    calc
      jf.val ≤ i + jf.val := Nat.le_add_left jf.val i
      _ = n := h
  rw [biproduct_ι_f_comp_tensorShiftedXIso_inv_of_le (hle := hle)]
  have hi : n - jf.val = i := by omega
  subst i
  rfl

private theorem biproduct_ι_f_comp_tensorShiftedXIso_inv_of_not_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n ≤ q + 1)
    (jf : Fin (q + 2)) (hle : ¬ jf.val ≤ n) :
    (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf).f n ≫
        (tensorShiftedXIso K P a q n hn).inv = 0 := by
  erw [tensorShiftedXIso, Iso.trans_inv, Iso.symm_inv, ← Category.assoc,
    biproduct_ι_f_comp_evalMapBiproduct_hom,
    biproduct_ι_comp_tensorShiftedBaseIso_inv]
  erw [shiftedTensorBackwardComponent_eq_of_not_le (hle := hle)]

private theorem tensorShiftedXIso_hom_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q n : ℕ) (hn : n + 1 ≤ q + 1) :
    (tensorShiftedXIso K P a q (n + 1) hn).hom ≫
        (finiteShiftedTensorComplex K P a q).d (n + 1) n =
      (tensorObj K (rowHomologyComplex P a)).d (n + 1) n ≫
        (tensorShiftedXIso K P a q n (by omega)).hom := by
  rw [← cancel_mono (tensorShiftedXIso K P a q n (by omega)).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply mapBifunctor.hom_ext
  intro i j h
  change i + j = n + 1 at h
  let jf : Fin (q + 2) := ⟨j, by omega⟩
  erw [ιTensorObj_comp_d_down_nat K (rowHomologyComplex P a) i j n h]
  rw [← Category.assoc, ιTensorObj_comp_tensorShiftedXIso_hom]
  simp only [Category.assoc]
  rw [
    (biproduct.ι
      (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)
      jf).comm_assoc]
  by_cases hi : i = 0
  · subst i
    have hjnot : ¬ jf.val ≤ n := by
      change ¬ j ≤ n
      omega
    erw [biproduct_ι_f_comp_tensorShiftedXIso_inv_of_not_le
      K P a q n (by omega) jf hjnot]
    simp
  · have hpred : i - 1 + j = n := by omega
    erw [biproduct_ι_f_comp_tensorShiftedXIso_inv_of_eq
      K P a q n (by omega) jf (i - 1) hpred]
    dsimp only [jf]
    have hTop : (shiftedTensorEmbedding j).f i = n + 1 :=
      (shiftedTensorEmbedding_f i j).trans h
    have hBottom : (shiftedTensorEmbedding j).f (i - 1) = n :=
      (shiftedTensorEmbedding_f (i - 1) j).trans hpred
    have hd : (shiftedTensorRowPiece K P a j).d (n + 1) n =
        (shiftedTensorRowPieceXIso K P a i j (n + 1) h).hom ≫
          (tensorRowPiece K P a j).d i (i - 1) ≫
          (shiftedTensorRowPieceXIso K P a (i - 1) j n hpred).inv := by
      exact (tensorRowPiece K P a j).extend_d_eq
        (e := shiftedTensorEmbedding j) hTop hBottom
    erw [hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (K.d i (i - 1) ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j)) ≫
        ιTensorObj K (rowHomologyComplex P a) (i - 1) j n hpred = _
    simp [hi]

private noncomputable def tensorShiftedShortComplexIsoZero
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).sc' 1 0 0 ≅
      (finiteShiftedTensorComplex K P a 0).sc' 1 0 0 :=
  ShortComplex.isoMk
    (tensorShiftedXIso K P a 0 1 (by omega))
    (tensorShiftedXIso K P a 0 0 (by omega))
    (tensorShiftedXIso K P a 0 0 (by omega))
    (tensorShiftedXIso_hom_d K P a 0 0 (by omega))
    (by
      have hs : ((tensorObj K (rowHomologyComplex P a)).sc' 1 0 0).g = 0 := by
        change (tensorObj K (rowHomologyComplex P a)).d 0 0 = 0
        exact (tensorObj K (rowHomologyComplex P a)).shape 0 0 (by simp)
      have ht : ((finiteShiftedTensorComplex K P a 0).sc' 1 0 0).g = 0 := by
        change (finiteShiftedTensorComplex K P a 0).d 0 0 = 0
        exact (finiteShiftedTensorComplex K P a 0).shape 0 0 (by simp)
      rw [hs, ht, comp_zero, zero_comp])

private noncomputable def tensorShiftedShortComplexIsoSucc
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a r : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).sc' (r + 2) (r + 1) r ≅
      (finiteShiftedTensorComplex K P a (r + 1)).sc' (r + 2) (r + 1) r :=
  ShortComplex.isoMk
    (tensorShiftedXIso K P a (r + 1) (r + 2) (by omega))
    (tensorShiftedXIso K P a (r + 1) (r + 1) (by omega))
    (tensorShiftedXIso K P a (r + 1) r (by omega))
    (tensorShiftedXIso_hom_d K P a (r + 1) (r + 1) (by omega))
    (tensorShiftedXIso_hom_d K P a (r + 1) r (by omega))

private noncomputable def tensorZeroRowHomologyFiniteIsoZero
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).homology 0 ≅
      (finiteShiftedTensorComplex K P a 0).homology 0 :=
  (tensorObj K (rowHomologyComplex P a)).homologyIsoSc' 1 0 0
      (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (tensorShiftedShortComplexIsoZero K P a) ≪≫
    ((finiteShiftedTensorComplex K P a 0).homologyIsoSc' 1 0 0
      (by simp) (by simp)).symm

private noncomputable def tensorZeroRowHomologyFiniteIsoSucc
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a r : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).homology (r + 1) ≅
      (finiteShiftedTensorComplex K P a (r + 1)).homology (r + 1) :=
  (tensorObj K (rowHomologyComplex P a)).homologyIsoSc'
      (r + 2) (r + 1) r (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (tensorShiftedShortComplexIsoSucc K P a r) ≪≫
    ((finiteShiftedTensorComplex K P a (r + 1)).homologyIsoSc'
      (r + 2) (r + 1) r (by simp) (by simp)).symm

private noncomputable def tensorZeroRowHomologyFiniteIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).homology q ≅
      (finiteShiftedTensorComplex K P a q).homology q :=
  match q with
  | 0 => tensorZeroRowHomologyFiniteIsoZero K P a
  | r + 1 => tensorZeroRowHomologyFiniteIsoSucc K P a r

private noncomputable def tensorZeroRowFiniteCyclesMapZero
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).cycles 0 ⟶
      (finiteShiftedTensorComplex K P a 0).cycles 0 :=
  ((tensorObj K (rowHomologyComplex P a)).cyclesIsoSc' 1 0 0
      (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (tensorShiftedShortComplexIsoZero K P a).hom ≫
    ((finiteShiftedTensorComplex K P a 0).cyclesIsoSc' 1 0 0
      (by simp) (by simp)).inv

private noncomputable def tensorZeroRowFiniteCyclesMapSucc
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a r : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).cycles (r + 1) ⟶
      (finiteShiftedTensorComplex K P a (r + 1)).cycles (r + 1) :=
  ((tensorObj K (rowHomologyComplex P a)).cyclesIsoSc'
      (r + 2) (r + 1) r (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (tensorShiftedShortComplexIsoSucc K P a r).hom ≫
    ((finiteShiftedTensorComplex K P a (r + 1)).cyclesIsoSc'
      (r + 2) (r + 1) r (by simp) (by simp)).inv

private noncomputable def tensorZeroRowFiniteCyclesMap
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).cycles q ⟶
      (finiteShiftedTensorComplex K P a q).cycles q :=
  match q with
  | 0 => tensorZeroRowFiniteCyclesMapZero K P a
  | r + 1 => tensorZeroRowFiniteCyclesMapSucc K P a r

@[reassoc]
private theorem homologyπ_comp_tensorZeroRowHomologyFiniteIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).homologyπ q ≫
        (tensorZeroRowHomologyFiniteIso K P a q).hom =
      tensorZeroRowFiniteCyclesMap K P a q ≫
        (finiteShiftedTensorComplex K P a q).homologyπ q := by
  cases q with
  | zero =>
      change (tensorObj K (rowHomologyComplex P a)).homologyπ 0 ≫
          (tensorZeroRowHomologyFiniteIsoZero K P a).hom =
        tensorZeroRowFiniteCyclesMapZero K P a ≫
          (finiteShiftedTensorComplex K P a 0).homologyπ 0
      unfold tensorZeroRowHomologyFiniteIsoZero
      unfold tensorZeroRowFiniteCyclesMapZero
      dsimp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso]
      rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
      rw [ShortComplex.homologyπ_naturality_assoc]
      rw [HomologicalComplex.π_homologyIsoSc'_inv]
      simp only [Category.assoc]
  | succ r =>
      change (tensorObj K (rowHomologyComplex P a)).homologyπ (r + 1) ≫
          (tensorZeroRowHomologyFiniteIsoSucc K P a r).hom =
        tensorZeroRowFiniteCyclesMapSucc K P a r ≫
          (finiteShiftedTensorComplex K P a (r + 1)).homologyπ (r + 1)
      unfold tensorZeroRowHomologyFiniteIsoSucc
      unfold tensorZeroRowFiniteCyclesMapSucc
      dsimp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso]
      rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
      rw [ShortComplex.homologyπ_naturality_assoc]
      rw [HomologicalComplex.π_homologyIsoSc'_inv]
      simp only [Category.assoc]

private theorem tensorZeroRowFiniteCyclesMap_iCycles
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    tensorZeroRowFiniteCyclesMap K P a q ≫
        (finiteShiftedTensorComplex K P a q).iCycles q =
      (tensorObj K (rowHomologyComplex P a)).iCycles q ≫
        (tensorShiftedXIso K P a q q (by omega)).hom := by
  cases q with
  | zero =>
      change tensorZeroRowFiniteCyclesMapZero K P a ≫
          (finiteShiftedTensorComplex K P a 0).iCycles 0 =
        (tensorObj K (rowHomologyComplex P a)).iCycles 0 ≫
          (tensorShiftedXIso K P a 0 0 (by omega)).hom
      let eS := (tensorObj K (rowHomologyComplex P a)).cyclesIsoSc' 1 0 0
        (by simp) (by simp)
      let eT := (finiteShiftedTensorComplex K P a 0).cyclesIsoSc' 1 0 0
        (by simp) (by simp)
      let φ := (tensorShiftedShortComplexIsoZero K P a).hom
      have hc := ShortComplex.cyclesMap_i φ
      change (eS.hom ≫ ShortComplex.cyclesMap φ ≫ eT.inv) ≫
          (finiteShiftedTensorComplex K P a 0).iCycles 0 = _
      calc
        _ = eS.hom ≫
            (ShortComplex.cyclesMap φ ≫
              ((finiteShiftedTensorComplex K P a 0).sc' 1 0 0).iCycles) := by
          rw [Category.assoc, Category.assoc]
          rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles]
        _ = eS.hom ≫
            (((tensorObj K (rowHomologyComplex P a)).sc' 1 0 0).iCycles ≫
              φ.τ₂) := congrArg (fun k => eS.hom ≫ k) hc
        _ = (eS.hom ≫
              ((tensorObj K (rowHomologyComplex P a)).sc' 1 0 0).iCycles) ≫
            φ.τ₂ := (Category.assoc _ _ _).symm
        _ = (tensorObj K (rowHomologyComplex P a)).iCycles 0 ≫ φ.τ₂ := by
          rw [HomologicalComplex.cyclesIsoSc'_hom_iCycles]
        _ = _ := by rfl
  | succ r =>
      change tensorZeroRowFiniteCyclesMapSucc K P a r ≫
          (finiteShiftedTensorComplex K P a (r + 1)).iCycles (r + 1) =
        (tensorObj K (rowHomologyComplex P a)).iCycles (r + 1) ≫
          (tensorShiftedXIso K P a (r + 1) (r + 1) (by omega)).hom
      let eS := (tensorObj K (rowHomologyComplex P a)).cyclesIsoSc'
        (r + 2) (r + 1) r (by simp) (by simp)
      let eT := (finiteShiftedTensorComplex K P a (r + 1)).cyclesIsoSc'
        (r + 2) (r + 1) r (by simp) (by simp)
      let φ := (tensorShiftedShortComplexIsoSucc K P a r).hom
      have hc := ShortComplex.cyclesMap_i φ
      change (eS.hom ≫ ShortComplex.cyclesMap φ ≫ eT.inv) ≫
          (finiteShiftedTensorComplex K P a (r + 1)).iCycles (r + 1) = _
      calc
        _ = eS.hom ≫
            (ShortComplex.cyclesMap φ ≫
              ((finiteShiftedTensorComplex K P a (r + 1)).sc'
                (r + 2) (r + 1) r).iCycles) := by
          rw [Category.assoc, Category.assoc]
          rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles]
        _ = eS.hom ≫
            (((tensorObj K (rowHomologyComplex P a)).sc'
                (r + 2) (r + 1) r).iCycles ≫ φ.τ₂) :=
          congrArg (fun k => eS.hom ≫ k) hc
        _ = (eS.hom ≫
              ((tensorObj K (rowHomologyComplex P a)).sc'
                (r + 2) (r + 1) r).iCycles) ≫ φ.τ₂ :=
          (Category.assoc _ _ _).symm
        _ = (tensorObj K (rowHomologyComplex P a)).iCycles (r + 1) ≫
            φ.τ₂ := by
          rw [HomologicalComplex.cyclesIsoSc'_hom_iCycles]
        _ = _ := by rfl

private structure TensorRowFunctorData
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j : ℕ) where
  homologyIso : (tensorRowPiece K P a j).homology i ≅
    K.homology i ⊗ (rowHomologyComplex P a).X j
  cyclesIso : (tensorRowPiece K P a j).cycles i ≅
    K.cycles i ⊗ (rowHomologyComplex P a).X j
  homologyπ_hom :
    (tensorRowPiece K P a j).homologyπ i ≫ homologyIso.hom =
      cyclesIso.hom ≫
        (K.homologyπ i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j))
  cyclesIso_hom_iCycles :
    cyclesIso.hom ≫
        (K.iCycles i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j)) =
      (tensorRowPiece K P a j).iCycles i

private noncomputable def tensorRowFunctorData
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j : ℕ) :
    TensorRowFunctorData K P a i j := by
  let Qj : ModuleCat.{u} R := (rowHomologyComplex P a).X j
  letI : Projective Qj :=
    (P.cartanEilenbergVerticalHomologyResolution j).projective a
  letI : Module.Projective R Qj := by infer_instance
  letI : Module.Flat R Qj := Module.Flat.of_projective
  let F := tensorRight Qj
  let S := K.sc i
  let hl := S.homologyData.left
  let eH₁ := (hl.map F).homologyIso
  let eH₂ : (hl.map F).H ≅ F.obj S.homology := by
    exact F.mapIso hl.homologyIso.symm
  let eH := eH₁ ≪≫ eH₂
  let eC₁ := (hl.map F).cyclesIso
  let eC₂ : (hl.map F).K ≅ F.obj S.cycles := by
    exact F.mapIso hl.cyclesIso.symm
  let eC := eC₁ ≪≫ eC₂
  have heH₂ : eH₂.hom = F.map hl.homologyIso.inv := rfl
  have heC₂ : eC₂.hom = F.map hl.cyclesIso.inv := rfl
  have hbase :
      (hl.π ≫ hl.homologyIso.inv : hl.K ⟶ S.homology) =
        (hl.cyclesIso.inv ≫ S.homologyπ : hl.K ⟶ S.homology) :=
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv S hl
  have hmap :
      (F.map (hl.π ≫ hl.homologyIso.inv) :
        F.obj hl.K ⟶ F.obj S.homology) =
      (F.map (hl.cyclesIso.inv ≫ S.homologyπ) :
        F.obj hl.K ⟶ F.obj S.homology) :=
    congrArg
      (fun k : hl.K ⟶ S.homology =>
        (F.map k : F.obj hl.K ⟶ F.obj S.homology)) hbase
  have hleft :
      ((hl.map F).π ≫ eH₂.hom :
        (hl.map F).K ⟶ F.obj S.homology) =
      (F.map (hl.π ≫ hl.homologyIso.inv) :
        F.obj hl.K ⟶ F.obj S.homology) := by
    rw [heH₂]
    exact (F.map_comp hl.π hl.homologyIso.inv).symm
  have hright :
      (F.map (hl.cyclesIso.inv ≫ S.homologyπ) :
        F.obj hl.K ⟶ F.obj S.homology) =
      (eC₂.hom ≫ F.map S.homologyπ :
        (hl.map F).K ⟶ F.obj S.homology) := by
    rw [heC₂]
    exact F.map_comp hl.cyclesIso.inv S.homologyπ
  have htyped : (hl.map F).π ≫ eH₂.hom =
      eC₂.hom ≫ F.map S.homologyπ :=
    Eq.trans hleft (Eq.trans hmap hright)
  have hπS : (S.map F).homologyπ ≫ eH.hom =
      eC.hom ≫ F.map S.homologyπ := by
    dsimp only [eH, eC, eH₁, eC₁, Iso.trans_hom]
    rw [Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    rw [cancel_epi]
    exact htyped
  have hπ : (tensorRowPiece K P a j).homologyπ i ≫ eH.hom =
      eC.hom ≫ (K.homologyπ i ⊗ₘ 𝟙 Qj) := by
    exact hπS
  have hCanonical : (S.mapCyclesIso F).hom = eC.hom := by
    rw [hl.mapCyclesIso_eq F]
  have hcycles : eC.hom ≫ (K.iCycles i ⊗ₘ 𝟙 Qj) =
      (tensorRowPiece K P a j).iCycles i := by
    rw [← hCanonical]
    exact S.mapCyclesIso_hom_iCycles F
  exact
    { homologyIso := eH
      cyclesIso := eC
      homologyπ_hom := hπ
      cyclesIso_hom_iCycles := hcycles }

private theorem tensor_homologyπ_comp_tensorRowFunctorData_homologyIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j : ℕ) :
    (K.homologyπ i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j)) ≫
        (tensorRowFunctorData K P a i j).homologyIso.inv =
      (tensorRowFunctorData K P a i j).cyclesIso.inv ≫
        (tensorRowPiece K P a j).homologyπ i := by
  let d := tensorRowFunctorData K P a i j
  rw [← cancel_epi d.cyclesIso.hom]
  have hw := congrArg (fun k => k ≫ d.homologyIso.inv) d.homologyπ_hom
  calc
    d.cyclesIso.hom ≫
          (K.homologyπ i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j)) ≫
          d.homologyIso.inv =
        (d.cyclesIso.hom ≫
          (K.homologyπ i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j))) ≫
          d.homologyIso.inv := (Category.assoc _ _ _).symm
    _ = ((tensorRowPiece K P a j).homologyπ i ≫
          d.homologyIso.hom) ≫ d.homologyIso.inv := hw.symm
    _ = (tensorRowPiece K P a j).homologyπ i := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = d.cyclesIso.hom ≫ d.cyclesIso.inv ≫
        (tensorRowPiece K P a j).homologyπ i := by
      rw [Iso.hom_inv_id_assoc]

@[reassoc]
private theorem tensorRowFunctorData_cyclesIso_inv_iCycles
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j : ℕ) :
    (tensorRowFunctorData K P a i j).cyclesIso.inv ≫
        (tensorRowPiece K P a j).iCycles i =
      K.iCycles i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j) := by
  let d := tensorRowFunctorData K P a i j
  rw [← cancel_epi d.cyclesIso.hom]
  change d.cyclesIso.hom ≫ d.cyclesIso.inv ≫
      (tensorRowPiece K P a j).iCycles i =
    d.cyclesIso.hom ≫
      (K.iCycles i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j))
  rw [Iso.hom_inv_id_assoc]
  exact d.cyclesIso_hom_iCycles.symm

private noncomputable abbrev shiftedTensorRowExtendHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (shiftedTensorRowPiece K P a j).homology q ≅
      (tensorRowPiece K P a j).homology (q - j) :=
  (tensorRowPiece K P a j).extendHomologyIso (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f (q - j) j).trans (Nat.sub_add_cancel hj))

private noncomputable abbrev shiftedTensorRowExtendHomologyIsoOfEq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (shiftedTensorRowPiece K P a j).homology q ≅
      (tensorRowPiece K P a j).homology i :=
  (tensorRowPiece K P a j).extendHomologyIso (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f i j).trans h)

private noncomputable abbrev shiftedTensorRowExtendCyclesIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (shiftedTensorRowPiece K P a j).cycles q ≅
      (tensorRowPiece K P a j).cycles (q - j) :=
  (tensorRowPiece K P a j).extendCyclesIso (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f (q - j) j).trans (Nat.sub_add_cancel hj))

private noncomputable abbrev shiftedTensorRowExtendCyclesIsoOfEq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (shiftedTensorRowPiece K P a j).cycles q ≅
      (tensorRowPiece K P a j).cycles i :=
  (tensorRowPiece K P a j).extendCyclesIso (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f i j).trans h)

@[reassoc]
private theorem homologyπ_comp_shiftedTensorRowExtendHomologyIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (tensorRowPiece K P a j).homologyπ (q - j) ≫
        (shiftedTensorRowExtendHomologyIso K P a q j hj).inv =
      (shiftedTensorRowExtendCyclesIso K P a q j hj).inv ≫
        (shiftedTensorRowPiece K P a j).homologyπ q := by
  exact (tensorRowPiece K P a j).homologyπ_extendHomologyIso_inv
    (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f (q - j) j).trans (Nat.sub_add_cancel hj))

@[reassoc]
private theorem shiftedTensorRowExtendCyclesIso_inv_iCycles
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (shiftedTensorRowExtendCyclesIso K P a q j hj).inv ≫
        (shiftedTensorRowPiece K P a j).iCycles q =
      (tensorRowPiece K P a j).iCycles (q - j) ≫
        (shiftedTensorRowPieceXIso K P a (q - j) j q
          (Nat.sub_add_cancel hj)).inv := by
  exact (tensorRowPiece K P a j).extendCyclesIso_inv_iCycles
    (shiftedTensorEmbedding j)
    ((shiftedTensorEmbedding_f (q - j) j).trans (Nat.sub_add_cancel hj))

private noncomputable def shiftedTensorRowHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (shiftedTensorRowPiece K P a j).homology q ≅
      K.homology (q - j) ⊗ (rowHomologyComplex P a).X j :=
  shiftedTensorRowExtendHomologyIso K P a q j hj ≪≫
    (tensorRowFunctorData K P a (q - j) j).homologyIso

private noncomputable def shiftedTensorRowHomologyIsoOfEq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (shiftedTensorRowPiece K P a j).homology q ≅
      K.homology i ⊗ (rowHomologyComplex P a).X j :=
  shiftedTensorRowExtendHomologyIsoOfEq K P a i j q h ≪≫
    (tensorRowFunctorData K P a i j).homologyIso

@[reassoc]
private theorem tensor_homologyπ_comp_shiftedTensorRowHomologyIsoOfEq_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (K.homologyπ i ⊗ₘ 𝟙 ((rowHomologyComplex P a).X j)) ≫
        (shiftedTensorRowHomologyIsoOfEq K P a i j q h).inv =
      (tensorRowFunctorData K P a i j).cyclesIso.inv ≫
        (shiftedTensorRowExtendCyclesIsoOfEq K P a i j q h).inv ≫
        (shiftedTensorRowPiece K P a j).homologyπ q := by
  unfold shiftedTensorRowHomologyIsoOfEq
  dsimp only [Iso.trans_inv]
  rw [← Category.assoc,
    tensor_homologyπ_comp_tensorRowFunctorData_homologyIso_inv]
  have hext : (tensorRowPiece K P a j).homologyπ i ≫
        (shiftedTensorRowExtendHomologyIsoOfEq K P a i j q h).inv =
      (shiftedTensorRowExtendCyclesIsoOfEq K P a i j q h).inv ≫
        (shiftedTensorRowPiece K P a j).homologyπ q := by
    exact (tensorRowPiece K P a j).homologyπ_extendHomologyIso_inv
      (shiftedTensorEmbedding j) ((shiftedTensorEmbedding_f i j).trans h)
  rw [Category.assoc, hext]

@[reassoc]
private theorem shiftedTensorRowExtendCyclesIsoOfEq_inv_iCycles
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (shiftedTensorRowExtendCyclesIsoOfEq K P a i j q h).inv ≫
        (shiftedTensorRowPiece K P a j).iCycles q =
      (tensorRowPiece K P a j).iCycles i ≫
        (shiftedTensorRowPieceXIso K P a i j q h).inv := by
  exact (tensorRowPiece K P a j).extendCyclesIso_inv_iCycles
    (shiftedTensorEmbedding j) ((shiftedTensorEmbedding_f i j).trans h)

@[reassoc]
private theorem zeroRowPairCycles_shifted_coordinate
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (𝟙 (K.cycles i) ⊗ₘ
        (P.bicomplex.X a).cyclesMap (rowProjection P a) j) ≫
      ChainGradedPairing.pairCycles
        (𝟙 (tensorObj K (rowHomologyComplex P a)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (rowHomologyComplex P a)))) i j ≫
      (cyclesIsoOfEq (tensorObj K (rowHomologyComplex P a)) h).hom ≫
      tensorZeroRowFiniteCyclesMap K P a q =
    (𝟙 (K.cycles i) ⊗ₘ (P.bicomplex.X a).homologyπ j) ≫
      (tensorRowFunctorData K P a i j).cyclesIso.inv ≫
      (shiftedTensorRowExtendCyclesIsoOfEq K P a i j q h).inv ≫
      (shiftedTensorRowPiece K P a j).cyclesMap
        (biproduct.ι
          (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)
          (⟨j, by omega⟩ : Fin (q + 2))) q := by
  rw [← cancel_mono ((finiteShiftedTensorComplex K P a q).iCycles q)]
  simp only [Category.assoc]
  rw [tensorZeroRowFiniteCyclesMap_iCycles]
  rw [HomologicalComplex.cyclesIsoOfEq_hom_iCycles_assoc]
  rw [ChainGradedPairing.pairCycles_i_assoc]
  unfold ChainGradedPairing.pair
  simp only [HomologicalComplex.id_f, Category.comp_id]
  rw [ιTensorObj_comp_XIsoOfEq_assoc]
  rw [ιTensorObj_comp_tensorShiftedXIso_hom]
  rw [HomologicalComplex.cyclesMap_i]
  rw [shiftedTensorRowExtendCyclesIsoOfEq_inv_iCycles_assoc]
  rw [tensorRowFunctorData_cyclesIso_inv_iCycles_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rw [HomologicalComplex.cyclesMap_i]
  rw [iCycles_comp_rowProjection_f]

@[reassoc]
private theorem zeroRowPairHomology_shifted_coordinate
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a i j q : ℕ) (h : i + j = q) :
    (𝟙 (K.homology i) ⊗ₘ homologyMap (rowProjection P a) j) ≫
      ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K (rowHomologyComplex P a)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (rowHomologyComplex P a)))) i j ≫
      (homologyIsoOfEq (tensorObj K (rowHomologyComplex P a)) h).hom ≫
      (tensorZeroRowHomologyFiniteIso K P a q).hom =
    (shiftedTensorRowHomologyIsoOfEq K P a i j q h).inv ≫
      homologyMap
        (biproduct.ι
          (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)
          (⟨j, by omega⟩ : Fin (q + 2))) q := by
  apply ChainGradedPairing.tensor_homologyπ_hom_ext
    (K₁ := K) (K₂ := P.bicomplex.X a) i j
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [HomologicalComplex.homologyπ_naturality]
  simp only [Category.comp_id]
  have hfactor :
      K.homologyπ i ⊗ₘ
          ((P.bicomplex.X a).cyclesMap (rowProjection P a) j ≫
            (rowHomologyComplex P a).homologyπ j) =
        (𝟙 (K.cycles i) ⊗ₘ
            (P.bicomplex.X a).cyclesMap (rowProjection P a) j) ≫
          (K.homologyπ i ⊗ₘ
            (rowHomologyComplex P a).homologyπ j) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hfactor]
  slice_lhs 2 3 =>
    rw [ChainGradedPairing.tensor_homologyπ_comp_pairHomology]
  slice_lhs 3 4 =>
    rw [HomologicalComplex.homologyπ_comp_homologyIsoOfEq_hom]
  slice_lhs 4 5 =>
    rw [homologyπ_comp_tensorZeroRowHomologyFiniteIso_hom]
  have hfactorR :
      K.homologyπ i ⊗ₘ (P.bicomplex.X a).homologyπ j =
        (𝟙 (K.cycles i) ⊗ₘ (P.bicomplex.X a).homologyπ j) ≫
          (K.homologyπ i ⊗ₘ
            𝟙 ((rowHomologyComplex P a).X j)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hfactorR]
  slice_rhs 2 3 =>
    rw [tensor_homologyπ_comp_shiftedTensorRowHomologyIsoOfEq_inv]
  slice_rhs 4 5 =>
    rw [HomologicalComplex.homologyπ_naturality]
  rw [zeroRowPairCycles_shifted_coordinate_assoc]

private theorem tensorRight_map_homologyπ_comp_shiftedTensorRowHomologyIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : j ≤ q) :
    (K.homologyπ (q - j) ⊗ₘ
          𝟙 ((rowHomologyComplex P a).X j)) ≫
        (shiftedTensorRowHomologyIso K P a q j hj).inv =
      (tensorRowFunctorData K P a (q - j) j).cyclesIso.inv ≫
        (shiftedTensorRowExtendCyclesIso K P a q j hj).inv ≫
        (shiftedTensorRowPiece K P a j).homologyπ q := by
  unfold shiftedTensorRowHomologyIso
  dsimp only [Iso.trans_inv]
  rw [← Category.assoc,
    tensor_homologyπ_comp_tensorRowFunctorData_homologyIso_inv]
  rw [Category.assoc,
    homologyπ_comp_shiftedTensorRowExtendHomologyIso_inv]

private theorem isZero_shiftedTensorRowPiece_homology_of_not_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q j : ℕ) (hj : ¬ j ≤ q) :
    IsZero ((shiftedTensorRowPiece K P a j).homology q) := by
  apply (tensorRowPiece K P a j).isZero_homology_extend_of_notMem_range
    (shiftedTensorEmbedding j) q
  intro i
  rw [shiftedTensorEmbedding_f]
  omega

private noncomputable def finiteShiftedTensorHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (finiteShiftedTensorComplex K P a q).homology q ≅
      ⨁ fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q := by
  let A : Fin (q + 2) → ChainComplex (ModuleCat.{u} R) ℕ := fun jf =>
    shiftedTensorRowPiece K P a jf.val
  let D := Discrete.functor A
  let F := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) q
  let HA : Fin (q + 2) → ModuleCat.{u} R := fun jf => F.obj (A jf)
  let eHomologyDiagram : (D ⋙ F) ≅ Discrete.functor HA :=
    Discrete.natIso fun _ => Iso.refl _
  letI : F.Additive := by infer_instance
  letI : PreservesFiniteBiproducts F := by infer_instance
  letI : PreservesColimit D F := by infer_instance
  exact
    F.mapIso (biproduct.isoCoproduct A) ≪≫
      preservesColimitIso F D ≪≫
      colim.mapIso eHomologyDiagram ≪≫
      (biproduct.isoCoproduct HA).symm

@[reassoc]
private theorem homologyMap_biproduct_ι_comp_finiteShiftedTensorHomologyIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) (jf : Fin (q + 2)) :
    homologyMap
        (biproduct.ι
          (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val) jf) q ≫
        (finiteShiftedTensorHomologyIso K P a q).hom =
      biproduct.ι
        (fun jf : Fin (q + 2) =>
          (shiftedTensorRowPiece K P a jf.val).homology q) jf := by
  let A : Fin (q + 2) → ChainComplex (ModuleCat.{u} R) ℕ := fun jf =>
    shiftedTensorRowPiece K P a jf.val
  let D := Discrete.functor A
  let F := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) q
  let HA : Fin (q + 2) → ModuleCat.{u} R := fun jf => F.obj (A jf)
  let eHomologyDiagram : (D ⋙ F) ≅ Discrete.functor HA :=
    Discrete.natIso fun _ => Iso.refl _
  let eFinite :=
    F.mapIso (biproduct.isoCoproduct A) ≪≫
      preservesColimitIso F D ≪≫
      colim.mapIso eHomologyDiagram ≪≫
      (biproduct.isoCoproduct HA).symm
  change F.map (biproduct.ι A jf) ≫ eFinite.hom = biproduct.ι HA jf
  simp only [eFinite, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc]
  rw [biproduct.isoCoproduct_hom]
  rw [biproduct.ι_desc]
  rw [ι_preservesColimitIso_hom_assoc]
  rw [colim_map]
  rw [ι_colimMap_assoc]
  simp
  rfl

private noncomputable abbrev zeroRowAntidiagonalFamily
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    KunnethAntidiagonal q → ModuleCat.{u} R := fun ij =>
  K.homology ij.val.1 ⊗ (rowHomologyComplex P a).X ij.val.2

private noncomputable def finiteShiftedPaddingForwardComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) (jf : Fin (q + 2)) :
    (shiftedTensorRowPiece K P a jf.val).homology q ⟶
      ⨁ zeroRowAntidiagonalFamily K P a q := by
  by_cases hle : jf.val ≤ q
  · exact (shiftedTensorRowHomologyIso K P a q jf.val hle).hom ≫
      biproduct.ι (zeroRowAntidiagonalFamily K P a q)
        (⟨(q - jf.val, jf.val),
          Finset.mem_antidiagonal.mpr (Nat.sub_add_cancel hle)⟩ :
            KunnethAntidiagonal q)
  · exact 0

private theorem finiteShiftedPaddingForwardComponent_eq_of_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) (jf : Fin (q + 2))
    (hle : jf.val ≤ q) :
    finiteShiftedPaddingForwardComponent K P a q jf =
      (shiftedTensorRowHomologyIso K P a q jf.val hle).hom ≫
        biproduct.ι (zeroRowAntidiagonalFamily K P a q)
          (⟨(q - jf.val, jf.val),
            Finset.mem_antidiagonal.mpr (Nat.sub_add_cancel hle)⟩ :
              KunnethAntidiagonal q) := by
  unfold finiteShiftedPaddingForwardComponent
  split_ifs
  rfl

private theorem finiteShiftedPaddingForwardComponent_eq_of_not_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) (jf : Fin (q + 2))
    (hle : ¬ jf.val ≤ q) :
    finiteShiftedPaddingForwardComponent K P a q jf = 0 := by
  unfold finiteShiftedPaddingForwardComponent
  split_ifs
  rfl

private noncomputable def finiteShiftedPaddingBackwardComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowAntidiagonalFamily K P a q ij ⟶
      ⨁ fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  have hsum : i + j = q := Finset.mem_antidiagonal.mp hij
  have hj : j ≤ q := by omega
  have hi : q - j = i := by omega
  subst i
  exact (shiftedTensorRowHomologyIso K P a q j hj).inv ≫
    biproduct.ι
      (fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q)
      (⟨j, by omega⟩ : Fin (q + 2))

private noncomputable def finiteShiftedPaddingIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (⨁ fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q) ≅
      ⨁ zeroRowAntidiagonalFamily K P a q := by
  let HS : Fin (q + 2) → ModuleCat.{u} R := fun jf =>
    (shiftedTensorRowPiece K P a jf.val).homology q
  let B := zeroRowAntidiagonalFamily K P a q
  let fwd : (⨁ HS) ⟶ ⨁ B :=
    biproduct.desc (finiteShiftedPaddingForwardComponent K P a q)
  let bwd : (⨁ B) ⟶ ⨁ HS :=
    biproduct.desc (finiteShiftedPaddingBackwardComponent K P a q)
  have hsource : fwd ≫ bwd = 𝟙 (⨁ HS) := by
    apply biproduct.hom_ext'
    intro jf
    rw [biproduct.ι_desc_assoc]
    by_cases hle : jf.val ≤ q
    · rw [finiteShiftedPaddingForwardComponent_eq_of_le (hle := hle)]
      rw [Category.assoc, biproduct.ι_desc]
      unfold finiteShiftedPaddingBackwardComponent
      simp only [Iso.hom_inv_id_assoc, Category.comp_id]
      rfl
    · rw [finiteShiftedPaddingForwardComponent_eq_of_not_le (hle := hle)]
      have hz := isZero_shiftedTensorRowPiece_homology_of_not_le
        K P a q jf.val hle
      exact hz.eq_of_src _ _
  have htarget : bwd ≫ fwd = 𝟙 (⨁ B) := by
    apply biproduct.hom_ext'
    rintro ⟨⟨i, j⟩, hij⟩
    have hsum : i + j = q := Finset.mem_antidiagonal.mp hij
    have hj : j ≤ q := by omega
    have hi : q - j = i := by omega
    subst i
    rw [biproduct.ι_desc_assoc]
    unfold finiteShiftedPaddingBackwardComponent
    rw [Category.assoc, biproduct.ι_desc]
    dsimp only [fwd]
    rw [finiteShiftedPaddingForwardComponent_eq_of_le (hle := hj)]
    simp only [Iso.inv_hom_id_assoc, Category.comp_id]
    rfl
  exact
    { hom := fwd
      inv := bwd
      hom_inv_id := hsource
      inv_hom_id := htarget }

private theorem biproduct_ι_comp_finiteShiftedPaddingIso_hom_of_le
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) (jf : Fin (q + 2))
    (hle : jf.val ≤ q) :
    biproduct.ι
        (fun jf : Fin (q + 2) =>
          (shiftedTensorRowPiece K P a jf.val).homology q) jf ≫
        (finiteShiftedPaddingIso K P a q).hom =
      (shiftedTensorRowHomologyIso K P a q jf.val hle).hom ≫
        biproduct.ι (zeroRowAntidiagonalFamily K P a q)
          (⟨(q - jf.val, jf.val),
            Finset.mem_antidiagonal.mpr (Nat.sub_add_cancel hle)⟩ :
              KunnethAntidiagonal q) := by
  unfold finiteShiftedPaddingIso
  rw [biproduct.ι_desc]
  rw [finiteShiftedPaddingForwardComponent_eq_of_le (hle := hle)]

@[reassoc]
private theorem biproduct_ι_comp_finiteShiftedPaddingIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    biproduct.ι
        (fun jf : Fin (q + 2) =>
          (shiftedTensorRowPiece K P a jf.val).homology q)
        (⟨ij.val.2, by
          have hij := Finset.mem_antidiagonal.mp ij.property
          omega⟩ : Fin (q + 2)) ≫
        (finiteShiftedPaddingIso K P a q).hom =
      (shiftedTensorRowHomologyIsoOfEq K P a
        ij.val.1 ij.val.2 q
        (Finset.mem_antidiagonal.mp ij.property)).hom ≫
        biproduct.ι (zeroRowAntidiagonalFamily K P a q) ij := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  have hsum : i + j = q := Finset.mem_antidiagonal.mp hij
  have hj : j ≤ q := by omega
  have hi : q - j = i := by omega
  subst i
  rw [biproduct_ι_comp_finiteShiftedPaddingIso_hom_of_le (hle := hj)]
  rfl

private noncomputable abbrev zeroRowSummandXIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowAntidiagonalFamily K P a q ij ≅
      (kunnethTorResolutionSummand K P ij).X a :=
  Iso.refl _

@[reassoc]
private theorem biproduct_ι_comp_kunnethEvaluationIso_inv_comp_zeroRowPairing_component
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        zeroRowPairing K P a q =
      zeroRowPairingComponent K P a q ij := by
  rw [zeroRowPairing]
  simp only [Iso.inv_hom_id_assoc]
  rw [biproduct.ι_desc]

@[reassoc]
private theorem biproduct_ι_comp_kunnethEvaluationIso_inv_comp_zeroRowPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        zeroRowPairing K P a q =
      (𝟙 (K.homology ij.val.1) ⊗ₘ
        ((rowHomotopyEquiv P a).toHomologyIso ij.val.2).hom) ≫
        ChainGradedPairing.pairHomology
          (𝟙 (tensorObj K (rowHomologyComplex P a)))
          (ChainGradedPairing.homologyDescentData
            (𝟙 (tensorObj K (rowHomologyComplex P a))))
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K (rowHomologyComplex P a))
          (Finset.mem_antidiagonal.mp ij.property)).hom := by
  calc
    biproduct.ι
          (fun ij : KunnethAntidiagonal q =>
            (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        zeroRowPairing K P a q =
      zeroRowPairingComponent K P a q ij :=
        biproduct_ι_comp_kunnethEvaluationIso_inv_comp_zeroRowPairing_component
          K P a q ij
    _ = _ := by rfl

private noncomputable def zeroRowShiftedIsoInvComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      (shiftedTensorRowPiece K P a ij.val.2).homology q := by
  exact (shiftedTensorRowHomologyIsoOfEq K P a
    ij.val.1 ij.val.2 q
    (Finset.mem_antidiagonal.mp ij.property)).inv

private noncomputable def zeroRowShiftedComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      (finiteShiftedTensorComplex K P a q).homology q := by
  exact zeroRowShiftedIsoInvComponent K P a q ij ≫
    homologyMap
      (biproduct.ι
        (fun jf : Fin (q + 2) => shiftedTensorRowPiece K P a jf.val)
        (⟨ij.val.2, by
          have hij := Finset.mem_antidiagonal.mp ij.property
          omega⟩ : Fin (q + 2))) q

@[reassoc]
private theorem zeroRowPairingComponent_comp_tensorZeroRowHomologyFiniteIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowPairingComponent K P a q ij ≫
        (tensorZeroRowHomologyFiniteIso K P a q).hom =
      zeroRowShiftedComponent K P a q ij := by
  unfold zeroRowPairingComponent
  unfold zeroRowShiftedComponent
  change (𝟙 (K.homology ij.val.1) ⊗ₘ
        homologyMap (rowProjection P a) ij.val.2) ≫
      ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K (rowHomologyComplex P a)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (rowHomologyComplex P a))))
        ij.val.1 ij.val.2 ≫
      (homologyIsoOfEq (tensorObj K (rowHomologyComplex P a))
        (Finset.mem_antidiagonal.mp ij.property)).hom ≫
      (tensorZeroRowHomologyFiniteIso K P a q).hom = _
  exact zeroRowPairHomology_shifted_coordinate K P a
    ij.val.1 ij.val.2 q (Finset.mem_antidiagonal.mp ij.property)

private noncomputable def zeroRowFiniteHomologyComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      ⨁ fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q := by
  exact zeroRowShiftedIsoInvComponent K P a q ij ≫
    biproduct.ι
      (fun jf : Fin (q + 2) =>
        (shiftedTensorRowPiece K P a jf.val).homology q)
      (⟨ij.val.2, by
        have hij := Finset.mem_antidiagonal.mp ij.property
        omega⟩ : Fin (q + 2))

@[reassoc]
private theorem zeroRowShiftedComponent_comp_finiteShiftedTensorHomologyIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowShiftedComponent K P a q ij ≫
        (finiteShiftedTensorHomologyIso K P a q).hom =
      zeroRowFiniteHomologyComponent K P a q ij := by
  unfold zeroRowShiftedComponent zeroRowFiniteHomologyComponent
  rw [Category.assoc,
    homologyMap_biproduct_ι_comp_finiteShiftedTensorHomologyIso_hom]

private noncomputable def zeroRowPaddingComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      ⨁ zeroRowAntidiagonalFamily K P a q := by
  exact zeroRowShiftedIsoInvComponent K P a q ij ≫
    (shiftedTensorRowHomologyIsoOfEq K P a
      ij.val.1 ij.val.2 q
      (Finset.mem_antidiagonal.mp ij.property)).hom ≫
    biproduct.ι (zeroRowAntidiagonalFamily K P a q) ij

@[reassoc]
private theorem zeroRowFiniteHomologyComponent_comp_finiteShiftedPaddingIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowFiniteHomologyComponent K P a q ij ≫
        (finiteShiftedPaddingIso K P a q).hom =
      zeroRowPaddingComponent K P a q ij := by
  unfold zeroRowFiniteHomologyComponent zeroRowPaddingComponent
  rw [Category.assoc, biproduct_ι_comp_finiteShiftedPaddingIso_hom]

private noncomputable def zeroRowSummandBiproductComponent
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).X a ⟶
      ⨁ fun ij : KunnethAntidiagonal q =>
        (kunnethTorResolutionSummand K P ij).X a :=
  zeroRowPaddingComponent K P a q ij ≫
    (biproduct.mapIso (zeroRowSummandXIso K P a q)).hom

@[reassoc]
private theorem zeroRowPaddingComponent_comp_biproductMapIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowPaddingComponent K P a q ij ≫
        (biproduct.mapIso (zeroRowSummandXIso K P a q)).hom =
      zeroRowSummandBiproductComponent K P a q ij := by
  rfl

@[reassoc]
private theorem zeroRowShiftedIsoInvComponent_comp_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowShiftedIsoInvComponent K P a q ij ≫
        (shiftedTensorRowHomologyIsoOfEq K P a
          ij.val.1 ij.val.2 q
          (Finset.mem_antidiagonal.mp ij.property)).hom =
      (zeroRowSummandXIso K P a q ij).inv := by
  unfold zeroRowShiftedIsoInvComponent
  exact (shiftedTensorRowHomologyIsoOfEq K P a
    ij.val.1 ij.val.2 q
    (Finset.mem_antidiagonal.mp ij.property)).inv_hom_id

@[reassoc]
private theorem zeroRowSummandBiproductComponent_eq_ι
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    zeroRowSummandBiproductComponent K P a q ij =
      biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          (kunnethTorResolutionSummand K P ij).X a) ij := by
  unfold zeroRowSummandBiproductComponent zeroRowPaddingComponent
  simp only [Category.assoc]
  rw [zeroRowShiftedIsoInvComponent_comp_hom_assoc]
  have hι : biproduct.ι (zeroRowAntidiagonalFamily K P a q) ij ≫
        (biproduct.mapIso (zeroRowSummandXIso K P a q)).hom =
      (zeroRowSummandXIso K P a q ij).hom ≫
        biproduct.ι
          (fun ij : KunnethAntidiagonal q =>
            (kunnethTorResolutionSummand K P ij).X a) ij := by
    exact biproduct.ι_map
      (fun ij => (zeroRowSummandXIso K P a q ij).hom) ij
  calc
    (zeroRowSummandXIso K P a q ij).inv ≫
          biproduct.ι (zeroRowAntidiagonalFamily K P a q) ij ≫
            (biproduct.mapIso (zeroRowSummandXIso K P a q)).hom =
        (zeroRowSummandXIso K P a q ij).inv ≫
          ((zeroRowSummandXIso K P a q ij).hom ≫
            biproduct.ι
              (fun ij : KunnethAntidiagonal q =>
                (kunnethTorResolutionSummand K P ij).X a) ij) :=
      congrArg (fun k => (zeroRowSummandXIso K P a q ij).inv ≫ k) hι
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

private noncomputable def zeroRowCollapseIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (tensorObj K (rowHomologyComplex P a)).homology q ≅
      (kunnethTorResolutionComplex K P q).X a :=
  tensorZeroRowHomologyFiniteIso K P a q ≪≫
    finiteShiftedTensorHomologyIso K P a q ≪≫
    finiteShiftedPaddingIso K P a q ≪≫
    biproduct.mapIso (zeroRowSummandXIso K P a q) ≪≫
    (kunnethEvaluationIso K P a q).symm

private theorem zeroRowPairing_comp_zeroRowCollapseIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    zeroRowPairing K P a q ≫ (zeroRowCollapseIso K P a q).hom = 𝟙 _ := by
  unfold zeroRowCollapseIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_epi (kunnethEvaluationIso K P a q).inv]
  apply biproduct.hom_ext'
  intro ij
  rw [biproduct_ι_comp_kunnethEvaluationIso_inv_comp_zeroRowPairing_component_assoc]
  rw [zeroRowPairingComponent_comp_tensorZeroRowHomologyFiniteIso_hom_assoc]
  rw [zeroRowShiftedComponent_comp_finiteShiftedTensorHomologyIso_hom_assoc]
  rw [zeroRowFiniteHomologyComponent_comp_finiteShiftedPaddingIso_hom_assoc]
  rw [zeroRowPaddingComponent_comp_biproductMapIso_hom_assoc]
  rw [zeroRowSummandBiproductComponent_eq_ι_assoc]
  simp only [Category.comp_id]

@[reassoc]
private theorem biproduct_ι_comp_kunnethEvaluationIso_inv_comp_actualPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ)
    (ij : KunnethAntidiagonal q) :
    biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        (kunnethCEVerticalHomologyPairing K P q).f a =
      actualRowPairingComponent K P a q ij :=
  (kunnethEvaluationData K P a q).pairing_component ij

private theorem kunnethCEVerticalHomologyPairing_f_comp_tensorRowHomologyIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    (kunnethCEVerticalHomologyPairing K P q).f a ≫
        (tensorRowHomologyIso K P a q).hom =
      zeroRowPairing K P a q := by
  rw [← cancel_epi (kunnethEvaluationIso K P a q).inv]
  apply biproduct.hom_ext'
  intro ij
  calc
    biproduct.ι
          (fun ij : KunnethAntidiagonal q =>
            (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        (kunnethCEVerticalHomologyPairing K P q).f a ≫
        (tensorRowHomologyIso K P a q).hom =
      actualRowPairingComponent K P a q ij ≫
        (tensorRowHomologyIso K P a q).hom :=
          biproduct_ι_comp_kunnethEvaluationIso_inv_comp_actualPairing_assoc
            K P a q ij (tensorRowHomologyIso K P a q).hom
    _ = zeroRowPairingComponent K P a q ij :=
      actualRowPairingComponent_comp_tensorRowHomologyIso_hom K P a q ij
    _ = biproduct.ι
          (fun ij : KunnethAntidiagonal q =>
            (kunnethTorResolutionSummand K P ij).X a) ij ≫
        (kunnethEvaluationIso K P a q).inv ≫
        zeroRowPairing K P a q :=
      (biproduct_ι_comp_kunnethEvaluationIso_inv_comp_zeroRowPairing_component
        K P a q ij).symm

private theorem zeroRowPairing_eq_zeroRowCollapseIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    zeroRowPairing K P a q = (zeroRowCollapseIso K P a q).inv := by
  rw [← cancel_mono (zeroRowCollapseIso K P a q).hom]
  rw [zeroRowPairing_comp_zeroRowCollapseIso_hom,
    (zeroRowCollapseIso K P a q).inv_hom_id]

private noncomputable def actualRowCollapseIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    ((kunnethCEBicomplex K P).verticalHomologyComplex q).X a ≅
      (kunnethTorResolutionComplex K P q).X a := by
  change (tensorObj K (P.bicomplex.X a)).homology q ≅
    (kunnethTorResolutionComplex K P q).X a
  exact tensorRowHomologyIso K P a q ≪≫ zeroRowCollapseIso K P a q

private theorem isIso_kunnethCEVerticalHomologyPairing_component
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (a q : ℕ) :
    IsIso ((kunnethCEVerticalHomologyPairing K P q).f a) := by
  let eActual := actualRowCollapseIso K P a q
  have heq : (kunnethCEVerticalHomologyPairing K P q).f a = eActual.inv := by
    rw [← cancel_mono eActual.hom]
    change ((kunnethCEVerticalHomologyPairing K P q).f a ≫
        (tensorRowHomologyIso K P a q).hom) ≫
          (zeroRowCollapseIso K P a q).hom = _
    rw [kunnethCEVerticalHomologyPairing_f_comp_tensorRowHomologyIso_hom]
    rw [zeroRowPairing_comp_zeroRowCollapseIso_hom]
    exact eActual.inv_hom_id.symm
  rw [heq]
  exact eActual.isIso_inv

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For each inner degree q, the canonical map from the finite antidiagonal Tor-resolution
complex to vertical homology of the tensor-convolution bicomplex is an isomorphism of
resolution-degree chain complexes. No flatness of K is assumed. -/
public theorem isIso_kunnethCEVerticalHomologyPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ) :
    IsIso (kunnethCEVerticalHomologyPairing K P q) := by
  let _ (a : ℕ) : IsIso ((kunnethCEVerticalHomologyPairing K P q).f a) :=
    isIso_kunnethCEVerticalHomologyPairing_component K P a q
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For each q ∈ ℕ, vertical homology of the tensor-convolution bicomplex is isomorphic to the
finite degree-q Tor-resolution complex. The inverse of this isomorphism is exactly the canonical
homogeneous tensor pairing. -/
public noncomputable def kunnethCEVerticalHomologyComplexIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (kunnethCEBicomplex K P).verticalHomologyComplex q ≅
      kunnethTorResolutionComplex K P q := by
  let _ := isIso_kunnethCEVerticalHomologyPairing K P q
  exact (asIso (kunnethCEVerticalHomologyPairing K P q)).symm

@[simp]
public theorem kunnethCEVerticalHomologyComplexIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (kunnethCEVerticalHomologyComplexIso K P q).inv =
      kunnethCEVerticalHomologyPairing K P q := by
  let _ := isIso_kunnethCEVerticalHomologyPairing K P q
  rfl

end HomologicalComplex

end
