/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.Grp.AddCommGrpProduct
public import MathlibExt.Algebra.Homology.ShortComplex.HomologyLimits
public import MathlibExt.Algebra.Homology.ChainComplex.HomCochainComplex
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public meta import Lean.Elab.Tactic.Omega

/-!
# Hom from a zero-differential source

The entire integer-indexed Hom product retains the target differential and
the source-convention sign. Exact products and the stated projectivity
hypotheses compute its cohomology; no finite-support condition is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v

namespace AddCommGrpCat

/-- The integer-indexed categorical limit is the full dependent-function group. -/
def intLimitIsoPi (F : Discrete ℤ ⥤ AddCommGrpCat.{v}) :
    limit F ≅ AddCommGrpCat.of (∀ r : ℤ, F.obj ⟨r⟩) :=
  discreteLimitIsoPi.{0, v} F

/-- The product comparison preserves every projection. -/
@[reassoc]
lemma intLimitIsoPi_hom_eval (F : Discrete ℤ ⥤ AddCommGrpCat.{v}) (r : ℤ) :
    (intLimitIsoPi F).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun r : ℤ => F.obj ⟨r⟩) r) =
      limit.π F ⟨r⟩ :=
  discreteLimitIsoPi_hom_eval.{0, v} F r

/-- The inverse comparison has the component of any full family. -/
@[reassoc]
lemma intLimitIsoPi_inv_π (F : Discrete ℤ ⥤ AddCommGrpCat.{v}) (r : ℤ) :
    (intLimitIsoPi F).inv ≫ limit.π F ⟨r⟩ =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun r : ℤ => F.obj ⟨r⟩) r) :=
  discreteLimitIsoPi_inv_π.{0, v} F r

end AddCommGrpCat

namespace ChainComplex

variable {C : Type u} [Category.{v} C]

section Coordinates

variable [Preadditive C]

/-- Full Hom cochains are all source-indexed morphisms at the matching target degree. -/
def homCochainPiEquiv (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n ≃+
      (∀ r : ℤ, P.X (-r) ⟶ Q.X (r + n)) where
  toFun z r := z.v r (r + n) rfl
  invFun f := CochainComplex.HomComplex.Cochain.mk
    (fun r q h => f r ≫ (Q.XIsoOfEq h).hom)
  left_inv z := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro r q h
    subst q
    simp only [CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  right_inv f := by
    funext r
    change f r ≫ 𝟙 (Q.X (r + n)) = f r
    exact Category.comp_id (f r)
  map_add' z z' := by
    funext r
    rfl

/-- Every source index remains an cochain component. -/
lemma homCochainPiEquiv_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n r : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    homCochainPiEquiv P Q n z r = z.v r (r + n) rfl := rfl

/-- The inverse takes an unrestricted family and earns the target-degree transport. -/
lemma homCochainPiEquiv_symm_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (f : ∀ r : ℤ, P.X (-r) ⟶ Q.X (r + n)) (r q : ℤ) (h : r + n = q) :
    ((homCochainPiEquiv P Q n).symm f).v r q h = f r ≫ (Q.XIsoOfEq h).hom := rfl

/-- Reindexing preserves the zero-source differential at every pair. -/
lemma reindexed_d_eq_zero (P : ChainComplex C ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (i j : ℤ) :
    ((cochainComplexEquivalence C).functor.obj P).d i j = 0 := by
  change P.d (-i) (-j) = 0
  exact hZero _ _

/-- A zero source leaves the target's postcomposition differential in Hom. -/
lemma rawHomZeroSource_d_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n)
    (r q : ℤ) (h : r + m = q) (q₀ : ℤ) (hq₀ : q₀ = q - 1) :
    (((CochainComplex.HomComplex
      ((cochainComplexEquivalence C).functor.obj P) Q).d n m).hom z).v r q h =
      z.v r q₀ (by omega) ≫ Q.d q₀ q := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let v : A.X r ⟶ Q.X q₀ := z.v r q₀ (by omega)
  let d : Q.X q₀ ⟶ Q.X q := Q.d q₀ q
  let w : A.X (r + 1) ⟶ Q.X q := z.v (r + 1) q (by omega)
  have hd : A.d r (r + 1) = 0 := reindexed_d_eq_zero P hZero r (r + 1)
  have hz : A.d r (r + 1) ≫ w = (0 : A.X r ⟶ Q.X q) :=
    (congrArg (fun a : A.X r ⟶ A.X (r + 1) => a ≫ w) hd).trans
      (CategoryTheory.Limits.zero_comp (f := w))
  have hδ : (CochainComplex.HomComplex.δ n m z).v r q h =
      v ≫ d + m.negOnePow • (A.d r (r + 1) ≫ w) :=
    CochainComplex.HomComplex.δ_v n m hnm z r q h q₀ (r + 1) hq₀ rfl
  change (CochainComplex.HomComplex.δ n m z).v r q h = v ≫ d
  exact hδ.trans
    ((congrArg (fun a : A.X r ⟶ Q.X q => v ≫ d + m.negOnePow • a) hz).trans
      ((congrArg (fun a : A.X r ⟶ Q.X q => v ≫ d + a)
        (smul_zero m.negOnePow)).trans (add_zero (v ≫ d))))

/-- In the source convention, the same target differential has its degree unit. -/
lemma homZeroSource_d_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n)
    (r q : ℤ) (h : r + m = q) :
    (((homCochainComplex P Q).d n m).hom z).v r q h =
      m.negOnePow • (z.v r (q - 1) (by omega) ≫ Q.d (q - 1) q) := by
  rw [homCochainComplex_d_v P Q n m hnm z r q h,
    reindexed_d_eq_zero P hZero, CategoryTheory.Limits.zero_comp, zero_add]

/-- The physical source degree uses the double-negation transport, with p+q=n. -/
def homCochainComponent (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) (p : ℤ) :
    P.X p ⟶ Q.X (n - p) :=
  (P.XIsoOfEq (Int.neg_neg p)).inv ≫ z.v (-p) (n - p) (by omega)

/-- The physical component retains both source and target maps. -/
lemma homCochainComponent_map {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n p : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    homCochainComponent P' Q' n (((homCochainComplexMap f g).f n).hom z) p =
      f.f p ≫ homCochainComponent P Q n z p ≫ g.f (n - p) := by
  let a : P'.X p ⟶ P'.X (-(-p)) := (P'.XIsoOfEq (Int.neg_neg p)).inv
  let b : P'.X (-(-p)) ⟶ P.X (-(-p)) := f.f (-(-p))
  let c : P'.X p ⟶ P.X p := f.f p
  let e : P.X p ⟶ P.X (-(-p)) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let v : P.X (-(-p)) ⟶ Q.X (n - p) := z.v (-p) (n - p) (by omega)
  let w : Q.X (n - p) ⟶ Q'.X (n - p) := g.f (n - p)
  have h : a ≫ b = c ≫ e :=
    (HomologicalComplex.XIsoOfEq_inv_naturality f (Int.neg_neg p)).symm
  have hv := homCochainComplexMap_v f g n (-p) (n - p) (by omega) z
  change a ≫ (((homCochainComplexMap f g).f n).hom z).v
      (-p) (n - p) (by omega) = c ≫ (e ≫ v) ≫ w
  calc
    _ = a ≫ b ≫ v ≫ w := congrArg (fun t => a ≫ t) hv
    _ = (a ≫ b) ≫ v ≫ w := (Category.assoc a b (v ≫ w)).symm
    _ = (c ≫ e) ≫ v ≫ w :=
      congrArg (fun t : P'.X p ⟶ P.X (-(-p)) => t ≫ v ≫ w) h
    _ = c ≫ (e ≫ v) ≫ w :=
      (Category.assoc c e (v ≫ w)).trans
        (congrArg (fun t : P.X p ⟶ Q'.X (n - p) => c ≫ t)
          (Category.assoc e v w).symm)

/-- Physical coordinates are additive on the cochain group. -/
lemma homCochainComponent_add (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n p : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    homCochainComponent P Q n (z + z') p =
      homCochainComponent P Q n z p + homCochainComponent P Q n z' p := by
  let a : P.X p ⟶ P.X (-(-p)) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let v : P.X (-(-p)) ⟶ Q.X (n - p) := z.v (-p) (n - p) (by omega)
  let v' : P.X (-(-p)) ⟶ Q.X (n - p) := z'.v (-p) (n - p) (by omega)
  change a ≫ (v + v') = a ≫ v + a ≫ v'
  exact Preadditive.comp_add (P.X p) (P.X (-(-p))) (Q.X (n - p)) a v v'

/-- A zero cochain has zero at every physical source degree. -/
lemma homCochainComponent_zero (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n p : ℤ) :
    homCochainComponent P Q n 0 p = 0 := by
  let a : P.X p ⟶ P.X (-(-p)) := (P.XIsoOfEq (Int.neg_neg p)).inv
  change a ≫ (0 : P.X (-(-p)) ⟶ Q.X (n - p)) = 0
  exact CategoryTheory.Limits.comp_zero (f := a)

/-- The target differential remains in physical coordinates, with the degree unit. -/
lemma homCochainComponent_d (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) (p : ℤ) :
    homCochainComponent P Q m (((homCochainComplex P Q).d n m).hom z) p =
      m.negOnePow • (homCochainComponent P Q n z p ≫ Q.d (n - p) (m - p)) := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let a : P.X p ⟶ A.X (-p) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let v : A.X (-p) ⟶ Q.X (n - p) := z.v (-p) (n - p) (by omega)
  let d : Q.X (n - p) ⟶ Q.X (m - p) := Q.d (n - p) (m - p)
  have hraw : (CochainComplex.HomComplex.δ n m z).v (-p) (m - p) (by omega) = v ≫ d :=
    rawHomZeroSource_d_v P Q hZero n m hnm z (-p) (m - p)
      (by omega) (n - p) (by omega)
  have hv : (((homCochainComplex P Q).d n m).hom z).v
      (-p) (m - p) (by omega) = m.negOnePow • (v ≫ d) := by
    change (m.negOnePow • CochainComplex.HomComplex.δ n m z).v
      (-p) (m - p) (by omega) = _
    exact (CochainComplex.HomComplex.Cochain.units_smul_v m.negOnePow
      (CochainComplex.HomComplex.δ n m z) (-p) (m - p) (by omega)).trans
        (congrArg (fun t : A.X (-p) ⟶ Q.X (m - p) => m.negOnePow • t) hraw)
  change a ≫ (((homCochainComplex P Q).d n m).hom z).v
      (-p) (m - p) (by omega) = m.negOnePow • ((a ≫ v) ≫ d)
  exact (congrArg (fun t : A.X (-p) ⟶ Q.X (m - p) => a ≫ t) hv).trans
    ((Linear.comp_units_smul a m.negOnePow (v ≫ d)).trans
      (congrArg (fun t : P.X p ⟶ Q.X (m - p) => m.negOnePow • t)
        (Category.assoc a v d).symm))

omit [Preadditive C] in
private lemma dependentHomFamily_transport {A B : ℤ → C}
    (f : ∀ p, A p ⟶ B p) {p p' : ℤ} (h : p = p') :
    (eqToIso (congrArg A h)).inv ≫ f p ≫ (eqToIso (congrArg B h)).hom = f p' := by
  subst p'
  simp

private lemma cochainComponent_transport {F G : CochainComplex C ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain F G n) (r r' q q' : ℤ)
    (h : r + n = q) (hr : r = r') (hq : q = q') :
    (F.XIsoOfEq hr).inv ≫ z.v r q h ≫ (G.XIsoOfEq hq).hom =
      z.v r' q' (by omega) := by
  subst r'
  subst q'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

/-- The full cochain group is the product over the physical source degrees. -/
def homCochainPhysicalPiEquiv (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n ≃+
      (∀ p : ℤ, P.X p ⟶ Q.X (n - p)) where
  toFun z p := homCochainComponent P Q n z p
  invFun f := CochainComplex.HomComplex.Cochain.mk
    (fun r q h => f (-r) ≫ (Q.XIsoOfEq (by omega : n - (-r) = q)).hom)
  left_inv z := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro r q h
    let F : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
    let a : F.X r ⟶ F.X (-(-r)) := (P.XIsoOfEq (Int.neg_neg (-r))).inv
    let v : F.X (-(-r)) ⟶ Q.X (n - (-r)) :=
      z.v (-(-r)) (n - (-r)) (by omega)
    let b : Q.X (n - (-r)) ⟶ Q.X q := (Q.XIsoOfEq (by omega)).hom
    have ha : a = (F.XIsoOfEq (Int.neg_neg r)).inv := rfl
    change (a ≫ v) ≫ b = z.v r q h
    exact (Category.assoc a v b).trans
      ((congrArg (fun t : F.X r ⟶ F.X (-(-r)) => t ≫ v ≫ b) ha).trans
        (cochainComponent_transport z (-(-r)) r (n - (-r)) q
          (by omega) (Int.neg_neg r) (by omega)))
  right_inv f := by
    funext p
    simp only [homCochainComponent, CochainComplex.HomComplex.Cochain.mk_v]
    change (eqToIso (congrArg P.X (Int.neg_neg p))).inv ≫ f (-(-p)) ≫
      (eqToIso (congrArg (fun p => Q.X (n - p)) (Int.neg_neg p))).hom = f p
    exact dependentHomFamily_transport f (Int.neg_neg p)
  map_add' z z' := by
    funext p
    exact homCochainComponent_add P Q n p z z'

/-- The physical product comparison is the component with its degree transport. -/
lemma homCochainPhysicalPiEquiv_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    homCochainPhysicalPiEquiv P Q n z p = homCochainComponent P Q n z p := rfl

/-- The inverse assembles every physical component into the full cochain. -/
lemma homCochainPhysicalPiEquiv_symm_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (f : ∀ p : ℤ, P.X p ⟶ Q.X (n - p)) (r q : ℤ) (h : r + n = q) :
    ((homCochainPhysicalPiEquiv P Q n).symm f).v r q h =
      f (-r) ≫ (Q.XIsoOfEq (by omega : n - (-r) = q)).hom := rfl

/-- The physical components retain the degree unit under scalar multiplication. -/
lemma homCochainComponent_units_smul (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (a : ℤˣ) (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    homCochainComponent P Q n (a • z) p = a • homCochainComponent P Q n z p := by
  let e : P.X p ⟶ P.X (-(-p)) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let v : P.X (-(-p)) ⟶ Q.X (n - p) := z.v (-p) (n - p) (by omega)
  change e ≫ (a • v) = a • (e ≫ v)
  exact Linear.comp_units_smul e a v

/-- Physical Hom coordinates before the sign change retain Q's differential. -/
lemma rawHomCochainComponent_d (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (n m : ℤ) (hnm : n + 1 = m)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) (p : ℤ) :
    homCochainComponent P Q m
        (((CochainComplex.HomComplex
          ((cochainComplexEquivalence C).functor.obj P) Q).d n m).hom z) p =
      homCochainComponent P Q n z p ≫ Q.d (n - p) (m - p) := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let a : P.X p ⟶ A.X (-p) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let v : A.X (-p) ⟶ Q.X (n - p) := z.v (-p) (n - p) (by omega)
  let d : Q.X (n - p) ⟶ Q.X (m - p) := Q.d (n - p) (m - p)
  have hv : (((CochainComplex.HomComplex A Q).d n m).hom z).v
      (-p) (m - p) (by omega) = v ≫ d :=
    rawHomZeroSource_d_v P Q hZero n m hnm z (-p) (m - p)
      (by omega) (n - p) (by omega)
  change a ≫ (((CochainComplex.HomComplex A Q).d n m).hom z).v
      (-p) (m - p) (by omega) = (a ≫ v) ≫ d
  exact (congrArg (fun t : A.X (-p) ⟶ Q.X (m - p) => a ≫ t) hv).trans
    (Category.assoc a v d).symm

/-- At each physical source degree, Hom is the adjacent Q short complex. -/
def homZeroSourceRow (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n p : ℤ) :
    ShortComplex AddCommGrpCat.{v} :=
  (Q.sc' (n - 1 - p) (n - p) (n + 1 - p)).map
    (preadditiveCoyoneda.obj (op (P.X p)))

/-- The row diagram includes every integer source degree, without a support condition. -/
def homZeroSourceRows (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    Discrete ℤ ⥤ ShortComplex AddCommGrpCat.{v} :=
  Discrete.functor (fun p => homZeroSourceRow P Q n p)

/-- The raw Hom short complex projects to each target-differential row. -/
def rawHomZeroSourceProjection (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ) :
    (CochainComplex.HomComplex
      ((cochainComplexEquivalence C).functor.obj P) Q).sc' (n - 1) n (n + 1) ⟶
        homZeroSourceRow P Q n p := by
  let a (k : ℤ) :
      AddCommGrpCat.of (CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj P) Q k) ⟶
        (preadditiveCoyoneda.obj (op (P.X p))).obj (Q.X (k - p)) :=
    AddCommGrpCat.ofHom ((Pi.evalAddMonoidHom (fun p => P.X p ⟶ Q.X (k - p)) p).comp
      (homCochainPhysicalPiEquiv P Q k).toAddMonoidHom)
  refine ShortComplex.homMk (a (n - 1)) (a n) (a (n + 1)) ?_ ?_
  · apply AddCommGrpCat.ext
    intro z
    change homCochainComponent P Q (n - 1) z p ≫ Q.d (n - 1 - p) (n - p) =
      homCochainComponent P Q n
        (((CochainComplex.HomComplex
          ((cochainComplexEquivalence C).functor.obj P) Q).d (n - 1) n).hom z) p
    exact (rawHomCochainComponent_d P Q hZero (n - 1) n (by omega) z p).symm
  · apply AddCommGrpCat.ext
    intro z
    change homCochainComponent P Q n z p ≫ Q.d (n - p) (n + 1 - p) =
      homCochainComponent P Q (n + 1)
        (((CochainComplex.HomComplex
          ((cochainComplexEquivalence C).functor.obj P) Q).d n (n + 1)).hom z) p
    exact (rawHomCochainComponent_d P Q hZero n (n + 1) rfl z p).symm

/-- The first projection retains the incoming-degree component. -/
lemma rawHomZeroSourceProjection_τ₁_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q (n - 1)) :
    (rawHomZeroSourceProjection P Q n hZero p).τ₁ z =
      homCochainComponent P Q (n - 1) z p := rfl

/-- The middle projection is the physical cochain component. -/
lemma rawHomZeroSourceProjection_τ₂_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    (rawHomZeroSourceProjection P Q n hZero p).τ₂ z = homCochainComponent P Q n z p := rfl

/-- The third projection retains the outgoing-degree component. -/
lemma rawHomZeroSourceProjection_τ₃_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q (n + 1)) :
    (rawHomZeroSourceProjection P Q n hZero p).τ₃ z =
      homCochainComponent P Q (n + 1) z p := rfl

/-- The raw Hom short complex is the full limit of its Q-differential rows. -/
def rawHomZeroSourceShortComplexIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) :
    (CochainComplex.HomComplex
      ((cochainComplexEquivalence C).functor.obj P) Q).sc' (n - 1) n (n + 1) ≅
        ShortComplex.limitShortComplex (homZeroSourceRows P Q n) := by
  let R : Discrete ℤ ⥤ ShortComplex AddCommGrpCat.{v} := homZeroSourceRows P Q n
  let K : ShortComplex AddCommGrpCat.{v} :=
    (CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) Q).sc'
      (n - 1) n (n + 1)
  let L : ShortComplex AddCommGrpCat.{v} := ShortComplex.limitShortComplex R
  let A (k : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q k)
  let B (k : ℤ) : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.X (k - p))
  let e (k : ℤ) : A k ≅ B k :=
    AddEquiv.toAddCommGrpIso (X := A k) (Y := B k) (homCochainPhysicalPiEquiv P Q k)
  let l₁ : limit (R ⋙ ShortComplex.π₁) ≅ B (n - 1) := by
    change limit (R ⋙ ShortComplex.π₁) ≅
      AddCommGrpCat.of (∀ p : ℤ, (R ⋙ ShortComplex.π₁).obj ⟨p⟩)
    exact AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₁)
  let l₂ : limit (R ⋙ ShortComplex.π₂) ≅ B n := by
    change limit (R ⋙ ShortComplex.π₂) ≅
      AddCommGrpCat.of (∀ p : ℤ, (R ⋙ ShortComplex.π₂).obj ⟨p⟩)
    exact AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₂)
  let l₃ : limit (R ⋙ ShortComplex.π₃) ≅ B (n + 1) := by
    change limit (R ⋙ ShortComplex.π₃) ≅
      AddCommGrpCat.of (∀ p : ℤ, (R ⋙ ShortComplex.π₃).obj ⟨p⟩)
    exact AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₃)
  let e₁ : K.X₁ ≅ L.X₁ := by
    change A (n - 1) ≅ limit (R ⋙ ShortComplex.π₁)
    exact e (n - 1) ≪≫ l₁.symm
  let e₂ : K.X₂ ≅ L.X₂ := by
    change A n ≅ limit (R ⋙ ShortComplex.π₂)
    exact e n ≪≫ l₂.symm
  let e₃ : K.X₃ ≅ L.X₃ := by
    change A (n + 1) ≅ limit (R ⋙ ShortComplex.π₃)
    exact e (n + 1) ≪≫ l₃.symm
  have h₁ (p : ℤ) : e₁.hom ≫ limit.π (R ⋙ ShortComplex.π₁) ⟨p⟩ =
      (rawHomZeroSourceProjection P Q n hZero p).τ₁ := by
    let π : limit (R ⋙ ShortComplex.π₁) ⟶ (R.obj ⟨p⟩).X₁ :=
      limit.π (R ⋙ ShortComplex.π₁) ⟨p⟩
    let v : B (n - 1) ⟶ (R.obj ⟨p⟩).X₁ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n - 1 - p)) p)
    have hl : l₁.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₁) p
    have he : (e (n - 1)).hom ≫ v =
        (rawHomZeroSourceProjection P Q n hZero p).τ₁ := rfl
    change ((e (n - 1)).hom ≫ l₁.inv) ≫ π = _
    exact (Category.assoc (e (n - 1)).hom l₁.inv π).trans
      ((congrArg (fun t : B (n - 1) ⟶ (R.obj ⟨p⟩).X₁ =>
        (e (n - 1)).hom ≫ t) hl).trans he)
  have h₂ (p : ℤ) : e₂.hom ≫ limit.π (R ⋙ ShortComplex.π₂) ⟨p⟩ =
      (rawHomZeroSourceProjection P Q n hZero p).τ₂ := by
    let π : limit (R ⋙ ShortComplex.π₂) ⟶ (R.obj ⟨p⟩).X₂ :=
      limit.π (R ⋙ ShortComplex.π₂) ⟨p⟩
    let v : B n ⟶ (R.obj ⟨p⟩).X₂ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n - p)) p)
    have hl : l₂.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₂) p
    have he : (e n).hom ≫ v =
        (rawHomZeroSourceProjection P Q n hZero p).τ₂ := rfl
    change ((e n).hom ≫ l₂.inv) ≫ π = _
    exact (Category.assoc (e n).hom l₂.inv π).trans
      ((congrArg (fun t : B n ⟶ (R.obj ⟨p⟩).X₂ => (e n).hom ≫ t) hl).trans he)
  have h₃ (p : ℤ) : e₃.hom ≫ limit.π (R ⋙ ShortComplex.π₃) ⟨p⟩ =
      (rawHomZeroSourceProjection P Q n hZero p).τ₃ := by
    let π : limit (R ⋙ ShortComplex.π₃) ⟶ (R.obj ⟨p⟩).X₃ :=
      limit.π (R ⋙ ShortComplex.π₃) ⟨p⟩
    let v : B (n + 1) ⟶ (R.obj ⟨p⟩).X₃ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n + 1 - p)) p)
    have hl : l₃.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₃) p
    have he : (e (n + 1)).hom ≫ v =
        (rawHomZeroSourceProjection P Q n hZero p).τ₃ := rfl
    change ((e (n + 1)).hom ≫ l₃.inv) ≫ π = _
    exact (Category.assoc (e (n + 1)).hom l₃.inv π).trans
      ((congrArg (fun t : B (n + 1) ⟶ (R.obj ⟨p⟩).X₃ =>
        (e (n + 1)).hom ≫ t) hl).trans he)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · apply limit.hom_ext
    intro j
    cases j with
    | mk p =>
      let ρ : L ⟶ R.obj ⟨p⟩ := ShortComplex.limitShortComplexProjection R ⟨p⟩
      let π₁ : L.X₁ ⟶ (R.obj ⟨p⟩).X₁ := limit.π (R ⋙ ShortComplex.π₁) ⟨p⟩
      let π₂ : L.X₂ ⟶ (R.obj ⟨p⟩).X₂ := limit.π (R ⋙ ShortComplex.π₂) ⟨p⟩
      let d : (R.obj ⟨p⟩).X₁ ⟶ (R.obj ⟨p⟩).X₂ := (R.obj ⟨p⟩).f
      have hρ₁ : ρ.τ₁ = π₁ := ShortComplex.limitShortComplexProjection_τ₁ R ⟨p⟩
      have hρ₂ : ρ.τ₂ = π₂ := ShortComplex.limitShortComplexProjection_τ₂ R ⟨p⟩
      have hL : L.f ≫ π₂ = π₁ ≫ d :=
        (congrArg (fun t : L.X₂ ⟶ (R.obj ⟨p⟩).X₂ => L.f ≫ t) hρ₂).symm.trans
          (ρ.comm₁₂.symm.trans
            (congrArg (fun t : L.X₁ ⟶ (R.obj ⟨p⟩).X₁ => t ≫ d) hρ₁))
      let ψ : K ⟶ R.obj ⟨p⟩ := rawHomZeroSourceProjection P Q n hZero p
      have hψ₁ : e₁.hom ≫ π₁ = ψ.τ₁ := h₁ p
      have hψ₂ : e₂.hom ≫ π₂ = ψ.τ₂ := h₂ p
      have h0 : (e₁.hom ≫ L.f) ≫ π₂ = e₁.hom ≫ (L.f ≫ π₂) :=
        Category.assoc e₁.hom L.f π₂
      have h1 : e₁.hom ≫ (L.f ≫ π₂) = (e₁.hom ≫ π₁) ≫ d :=
        (congrArg (fun t : L.X₁ ⟶ (R.obj ⟨p⟩).X₂ => e₁.hom ≫ t) hL).trans
          (Category.assoc e₁.hom π₁ d).symm
      have h2 : (e₁.hom ≫ π₁) ≫ d = ψ.τ₁ ≫ d :=
        congrArg (fun t : K.X₁ ⟶ (R.obj ⟨p⟩).X₁ => t ≫ d) hψ₁
      have h3 : ψ.τ₁ ≫ d = K.f ≫ ψ.τ₂ := ψ.comm₁₂
      have h4 : K.f ≫ ψ.τ₂ = (K.f ≫ e₂.hom) ≫ π₂ :=
        (congrArg (fun t : K.X₂ ⟶ (R.obj ⟨p⟩).X₂ => K.f ≫ t) hψ₂.symm).trans
          (Category.assoc K.f e₂.hom π₂).symm
      change (e₁.hom ≫ L.f) ≫ π₂ = (K.f ≫ e₂.hom) ≫ π₂
      exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
  · apply limit.hom_ext
    intro j
    cases j with
    | mk p =>
      let ρ : L ⟶ R.obj ⟨p⟩ := ShortComplex.limitShortComplexProjection R ⟨p⟩
      let π₂ : L.X₂ ⟶ (R.obj ⟨p⟩).X₂ := limit.π (R ⋙ ShortComplex.π₂) ⟨p⟩
      let π₃ : L.X₃ ⟶ (R.obj ⟨p⟩).X₃ := limit.π (R ⋙ ShortComplex.π₃) ⟨p⟩
      let d : (R.obj ⟨p⟩).X₂ ⟶ (R.obj ⟨p⟩).X₃ := (R.obj ⟨p⟩).g
      have hρ₂ : ρ.τ₂ = π₂ := ShortComplex.limitShortComplexProjection_τ₂ R ⟨p⟩
      have hρ₃ : ρ.τ₃ = π₃ := ShortComplex.limitShortComplexProjection_τ₃ R ⟨p⟩
      have hL : L.g ≫ π₃ = π₂ ≫ d :=
        (congrArg (fun t : L.X₃ ⟶ (R.obj ⟨p⟩).X₃ => L.g ≫ t) hρ₃).symm.trans
          (ρ.comm₂₃.symm.trans
            (congrArg (fun t : L.X₂ ⟶ (R.obj ⟨p⟩).X₂ => t ≫ d) hρ₂))
      let ψ : K ⟶ R.obj ⟨p⟩ := rawHomZeroSourceProjection P Q n hZero p
      have hψ₂ : e₂.hom ≫ π₂ = ψ.τ₂ := h₂ p
      have hψ₃ : e₃.hom ≫ π₃ = ψ.τ₃ := h₃ p
      have h0 : (e₂.hom ≫ L.g) ≫ π₃ = e₂.hom ≫ (L.g ≫ π₃) :=
        Category.assoc e₂.hom L.g π₃
      have h1 : e₂.hom ≫ (L.g ≫ π₃) = (e₂.hom ≫ π₂) ≫ d :=
        (congrArg (fun t : L.X₂ ⟶ (R.obj ⟨p⟩).X₃ => e₂.hom ≫ t) hL).trans
          (Category.assoc e₂.hom π₂ d).symm
      have h2 : (e₂.hom ≫ π₂) ≫ d = ψ.τ₂ ≫ d :=
        congrArg (fun t : K.X₂ ⟶ (R.obj ⟨p⟩).X₂ => t ≫ d) hψ₂
      have h3 : ψ.τ₂ ≫ d = K.g ≫ ψ.τ₃ := ψ.comm₂₃
      have h4 : K.g ≫ ψ.τ₃ = (K.g ≫ e₃.hom) ≫ π₃ :=
        (congrArg (fun t : K.X₃ ⟶ (R.obj ⟨p⟩).X₃ => K.g ≫ t) hψ₃.symm).trans
          (Category.assoc K.g e₃.hom π₃).symm
      change (e₂.hom ≫ L.g) ≫ π₃ = (K.g ≫ e₃.hom) ≫ π₃
      exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

/-- The limit comparison has exactly the physical row projection. -/
lemma rawHomZeroSourceShortComplexIso_hom_projection (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ) :
    (rawHomZeroSourceShortComplexIso P Q n hZero).hom ≫
        ShortComplex.limitShortComplexProjection (homZeroSourceRows P Q n) ⟨p⟩ =
      rawHomZeroSourceProjection P Q n hZero p := by
  let R : Discrete ℤ ⥤ ShortComplex AddCommGrpCat.{v} := homZeroSourceRows P Q n
  let A (k : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q k)
  let B (k : ℤ) : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.X (k - p))
  let e (k : ℤ) : A k ≅ B k :=
    AddEquiv.toAddCommGrpIso (X := A k) (Y := B k) (homCochainPhysicalPiEquiv P Q k)
  apply ShortComplex.hom_ext
  · let l : limit (R ⋙ ShortComplex.π₁) ≅ B (n - 1) :=
      AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₁)
    let π : limit (R ⋙ ShortComplex.π₁) ⟶ (R.obj ⟨p⟩).X₁ :=
      limit.π (R ⋙ ShortComplex.π₁) ⟨p⟩
    let v : B (n - 1) ⟶ (R.obj ⟨p⟩).X₁ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n - 1 - p)) p)
    have hl : l.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₁) p
    have hp : (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₁ = π :=
      ShortComplex.limitShortComplexProjection_τ₁ R ⟨p⟩
    change ((e (n - 1)).hom ≫ l.inv) ≫
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₁ = _
    exact (congrArg (fun t => ((e (n - 1)).hom ≫ l.inv) ≫ t) hp).trans
      ((Category.assoc (e (n - 1)).hom l.inv π).trans
        ((congrArg (fun t => (e (n - 1)).hom ≫ t) hl).trans (by rfl)))
  · let l : limit (R ⋙ ShortComplex.π₂) ≅ B n :=
      AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₂)
    let π : limit (R ⋙ ShortComplex.π₂) ⟶ (R.obj ⟨p⟩).X₂ :=
      limit.π (R ⋙ ShortComplex.π₂) ⟨p⟩
    let v : B n ⟶ (R.obj ⟨p⟩).X₂ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n - p)) p)
    have hl : l.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₂) p
    have hp : (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₂ = π :=
      ShortComplex.limitShortComplexProjection_τ₂ R ⟨p⟩
    change ((e n).hom ≫ l.inv) ≫
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₂ = _
    exact (congrArg (fun t => ((e n).hom ≫ l.inv) ≫ t) hp).trans
      ((Category.assoc (e n).hom l.inv π).trans
        ((congrArg (fun t => (e n).hom ≫ t) hl).trans (by rfl)))
  · let l : limit (R ⋙ ShortComplex.π₃) ≅ B (n + 1) :=
      AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₃)
    let π : limit (R ⋙ ShortComplex.π₃) ⟶ (R.obj ⟨p⟩).X₃ :=
      limit.π (R ⋙ ShortComplex.π₃) ⟨p⟩
    let v : B (n + 1) ⟶ (R.obj ⟨p⟩).X₃ := AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.X (n + 1 - p)) p)
    have hl : l.inv ≫ π = v :=
      AddCommGrpCat.intLimitIsoPi_inv_π (R ⋙ ShortComplex.π₃) p
    have hp : (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₃ = π :=
      ShortComplex.limitShortComplexProjection_τ₃ R ⟨p⟩
    change ((e (n + 1)).hom ≫ l.inv) ≫
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₃ = _
    exact (congrArg (fun t => ((e (n + 1)).hom ≫ l.inv) ≫ t) hp).trans
      ((Category.assoc (e (n + 1)).hom l.inv π).trans
        ((congrArg (fun t => (e (n + 1)).hom ≫ t) hl).trans (by rfl)))

end Coordinates

section CohomologyMap

variable [Abelian C]

/-- An full-Hom cycle supplies a canonical cycle in Q at each physical component. -/
def homZeroSourceCycleComponent (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0)
    (z : (homCochainComplex P Q).cycles n) (p : ℤ) : P.X p ⟶ Q.cycles (n - p) := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let A (k : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q k)
  let ι : H.cycles n ⟶ A n := H.iCycles n
  let δ : A n ⟶ A (n + 1) := H.d n (n + 1)
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n := ι.hom z
  let k : P.X p ⟶ Q.X (n - p) := homCochainComponent P Q n γ p
  have hιδ : ι ≫ δ = 0 := H.iCycles_d n (n + 1)
  have hz : δ.hom γ = (0 : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q (n + 1)) :=
    (AddCommGrpCat.comp_apply ι δ z).symm.trans
      (ConcreteCategory.congr_hom hιδ z)
  have hd : (n + 1).negOnePow • (k ≫ Q.d (n - p) (n + 1 - p)) = 0 :=
    (homCochainComponent_d P Q hZero n (n + 1) rfl γ p).symm.trans
      ((congrArg (fun a : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj P) Q (n + 1) =>
          homCochainComponent P Q (n + 1) a p) hz).trans
        (homCochainComponent_zero P Q (n + 1) p))
  have hk₀ : k ≫ Q.d (n - p) (n + 1 - p) = 0 := by
    have h := congrArg (fun a : P.X p ⟶ Q.X (n + 1 - p) =>
      (n + 1).negOnePow • a) hd
    simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using h
  have hk : k ≫ Q.d (n - p) (n - p + 1) = 0 := by
    have hq : n + 1 - p = n - p + 1 := by omega
    have hProp :
        (k ≫ Q.d (n - p) (n + 1 - p) = (0 : P.X p ⟶ Q.X (n + 1 - p))) =
          (k ≫ Q.d (n - p) (n - p + 1) = (0 : P.X p ⟶ Q.X (n - p + 1))) :=
      congrArg (fun j : ℤ => k ≫ Q.d (n - p) j = (0 : P.X p ⟶ Q.X j)) hq
    exact Eq.mp hProp hk₀
  have hj : (ComplexShape.up ℤ).next (n - p) = n - p + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n - p) (n - p + 1) rfl)
  exact Q.liftCycles (i := n - p) k (n - p + 1) hj hk

/-- The canonical cycle lift retains the physical cochain component. -/
@[reassoc]
lemma homZeroSourceCycleComponent_i (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0)
    (z : (homCochainComplex P Q).cycles n) (p : ℤ) :
    homZeroSourceCycleComponent P Q n hZero z p ≫ Q.iCycles (n - p) =
      homCochainComponent P Q n (((homCochainComplex P Q).iCycles n).hom z) p := by
  unfold homZeroSourceCycleComponent
  exact Q.liftCycles_i _ _ _ _

/-- The cycle lift is additive; no section of complexes is chosen. -/
lemma homZeroSourceCycleComponent_add (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0)
    (z z' : (homCochainComplex P Q).cycles n) (p : ℤ) :
    homZeroSourceCycleComponent P Q n hZero (z + z') p =
      homZeroSourceCycleComponent P Q n hZero z p +
        homZeroSourceCycleComponent P Q n hZero z' p := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n)
  let ι : H.cycles n ⟶ A := H.iCycles n
  let i : Q.cycles (n - p) ⟶ Q.X (n - p) := Q.iCycles (n - p)
  let c : P.X p ⟶ Q.cycles (n - p) :=
    homZeroSourceCycleComponent P Q n hZero (z + z') p
  let c₁ : P.X p ⟶ Q.cycles (n - p) := homZeroSourceCycleComponent P Q n hZero z p
  let c₂ : P.X p ⟶ Q.cycles (n - p) := homZeroSourceCycleComponent P Q n hZero z' p
  have hι : ι.hom (z + z') = ι.hom z + ι.hom z' := ι.hom.map_add z z'
  have h : homCochainComponent P Q n (ι.hom (z + z')) p =
      homCochainComponent P Q n (ι.hom z) p +
        homCochainComponent P Q n (ι.hom z') p :=
    (congrArg (fun a : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n =>
        homCochainComponent P Q n a p) hι).trans
      (homCochainComponent_add P Q n p (ι.hom z) (ι.hom z'))
  have hc : c ≫ i = homCochainComponent P Q n (ι.hom (z + z')) p :=
    homZeroSourceCycleComponent_i P Q n hZero (z + z') p
  have h₁ : c₁ ≫ i = homCochainComponent P Q n (ι.hom z) p :=
    homZeroSourceCycleComponent_i P Q n hZero z p
  have h₂ : c₂ ≫ i = homCochainComponent P Q n (ι.hom z') p :=
    homZeroSourceCycleComponent_i P Q n hZero z' p
  apply (cancel_mono i).1
  change c ≫ i = (c₁ + c₂) ≫ i
  exact hc.trans (h.trans
    ((congrArg₂ (fun a b : P.X p ⟶ Q.X (n - p) => a + b) h₁.symm h₂.symm).trans
      (Preadditive.add_comp (P.X p) (Q.cycles (n - p))
        (Q.X (n - p)) c₁ c₂ i).symm))

/-- The canonical cycle lift takes zero to zero. -/
lemma homZeroSourceCycleComponent_zero (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (p : ℤ) :
    homZeroSourceCycleComponent P Q n hZero 0 p = 0 := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n)
  let ι : H.cycles n ⟶ A := H.iCycles n
  let i : Q.cycles (n - p) ⟶ Q.X (n - p) := Q.iCycles (n - p)
  let c : P.X p ⟶ Q.cycles (n - p) := homZeroSourceCycleComponent P Q n hZero 0 p
  have hι : ι.hom (0 : H.cycles n) =
      (0 : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj P) Q n) := ι.hom.map_zero
  have h : homCochainComponent P Q n (ι.hom 0) p = 0 :=
    (congrArg (fun a : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n =>
        homCochainComponent P Q n a p) hι).trans
      (homCochainComponent_zero P Q n p)
  have hc : c ≫ i = homCochainComponent P Q n (ι.hom 0) p :=
    homZeroSourceCycleComponent_i P Q n hZero 0 p
  apply (cancel_mono i).1
  change c ≫ i = (0 : P.X p ⟶ Q.cycles (n - p)) ≫ i
  exact hc.trans (h.trans (CategoryTheory.Limits.zero_comp (f := i)).symm)

/-- Both variable maps act on the Q-cycle component. -/
lemma homZeroSourceCycleComponent_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n p : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (hZero' : ∀ i j : ℤ, P'.d i j = 0)
    (z : (homCochainComplex P Q).cycles n) :
    homZeroSourceCycleComponent P' Q' n hZero'
        (HomologicalComplex.cyclesMap (homCochainComplexMap f g) n z) p =
      f.f p ≫ homZeroSourceCycleComponent P Q n hZero z p ≫
        HomologicalComplex.cyclesMap g (n - p) := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let H' : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P' Q'
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n)
  let A' : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P') Q' n)
  let a : H ⟶ H' := homCochainComplexMap f g
  let l : H.cycles n ⟶ H'.cycles n := HomologicalComplex.cyclesMap a n
  let ι : H.cycles n ⟶ A := H.iCycles n
  let ι' : H'.cycles n ⟶ A' := H'.iCycles n
  let m : A ⟶ A' := a.f n
  have hι : l ≫ ι' = ι ≫ m := HomologicalComplex.cyclesMap_i a n
  have hPoint : ι'.hom (l.hom z) = m.hom (ι.hom z) :=
    (AddCommGrpCat.comp_apply l ι' z).symm.trans
      ((ConcreteCategory.congr_hom hι z).trans (AddCommGrpCat.comp_apply ι m z))
  let c : P.X p ⟶ Q.cycles (n - p) := homZeroSourceCycleComponent P Q n hZero z p
  let c' : P'.X p ⟶ Q'.cycles (n - p) :=
    homZeroSourceCycleComponent P' Q' n hZero' (l.hom z) p
  let i : Q.cycles (n - p) ⟶ Q.X (n - p) := Q.iCycles (n - p)
  let i' : Q'.cycles (n - p) ⟶ Q'.X (n - p) := Q'.iCycles (n - p)
  let b : Q.cycles (n - p) ⟶ Q'.cycles (n - p) :=
    HomologicalComplex.cyclesMap g (n - p)
  let t : P'.X p ⟶ P.X p := f.f p
  let v : Q.X (n - p) ⟶ Q'.X (n - p) := g.f (n - p)
  have hb : b ≫ i' = i ≫ v := HomologicalComplex.cyclesMap_i g (n - p)
  have hc : c ≫ i = homCochainComponent P Q n (ι.hom z) p :=
    homZeroSourceCycleComponent_i P Q n hZero z p
  have hc' : c' ≫ i' = homCochainComponent P' Q' n (ι'.hom (l.hom z)) p :=
    homZeroSourceCycleComponent_i P' Q' n hZero' (l.hom z) p
  have hRight : (t ≫ c ≫ b) ≫ i' = t ≫ (c ≫ i) ≫ v :=
    (Category.assoc t (c ≫ b) i').trans
      (congrArg (fun e : P.X p ⟶ Q'.X (n - p) => t ≫ e)
        ((Category.assoc c b i').trans
          ((congrArg (fun e : Q.cycles (n - p) ⟶ Q'.X (n - p) => c ≫ e) hb).trans
            (Category.assoc c i v).symm)))
  apply (cancel_mono i').1
  change c' ≫ i' = (t ≫ c ≫ b) ≫ i'
  exact hc'.trans
    ((congrArg (fun e : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P') Q' n =>
        homCochainComponent P' Q' n e p) hPoint).trans
      ((homCochainComponent_map f g n p (ι.hom z)).trans
        ((congrArg (fun e : P.X p ⟶ Q.X (n - p) => t ≫ e ≫ v) hc.symm).trans
          hRight.symm)))

/-- The Q-cycle components give the full cohomology-product map on Hom cycles. -/
def homZeroSourceCycleMap (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) :
    (homCochainComplex P Q).cycles n ⟶
      AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let F : H.cycles n →+ (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) :=
    { toFun z p := Int.triangularSign n •
        (homZeroSourceCycleComponent P Q n hZero z p ≫ Q.homologyπ (n - p))
      map_zero' := by
        funext p
        let c : P.X p ⟶ Q.cycles (n - p) :=
          homZeroSourceCycleComponent P Q n hZero (0 : H.cycles n) p
        let π : Q.cycles (n - p) ⟶ Q.homology (n - p) := Q.homologyπ (n - p)
        have hc : c = 0 := homZeroSourceCycleComponent_zero P Q n hZero p
        change Int.triangularSign n • (c ≫ π) = 0
        exact (congrArg (fun t : P.X p ⟶ Q.cycles (n - p) =>
          Int.triangularSign n • (t ≫ π)) hc).trans
          ((congrArg (fun t : P.X p ⟶ Q.homology (n - p) =>
            Int.triangularSign n • t) (CategoryTheory.Limits.zero_comp (f := π))).trans
              (smul_zero (Int.triangularSign n)))
      map_add' z z' := by
        funext p
        let c : P.X p ⟶ Q.cycles (n - p) :=
          homZeroSourceCycleComponent P Q n hZero (z + z') p
        let c₁ : P.X p ⟶ Q.cycles (n - p) :=
          homZeroSourceCycleComponent P Q n hZero z p
        let c₂ : P.X p ⟶ Q.cycles (n - p) :=
          homZeroSourceCycleComponent P Q n hZero z' p
        let π : Q.cycles (n - p) ⟶ Q.homology (n - p) := Q.homologyπ (n - p)
        have hc : c = c₁ + c₂ :=
          homZeroSourceCycleComponent_add P Q n hZero z z' p
        change Int.triangularSign n • (c ≫ π) =
          Int.triangularSign n • (c₁ ≫ π) + Int.triangularSign n • (c₂ ≫ π)
        exact (congrArg (fun t : P.X p ⟶ Q.cycles (n - p) =>
          Int.triangularSign n • (t ≫ π)) hc).trans
          ((congrArg (fun t : P.X p ⟶ Q.homology (n - p) =>
            Int.triangularSign n • t) (Preadditive.add_comp (P.X p) (Q.cycles (n - p))
            (Q.homology (n - p)) c₁ c₂ π)).trans
              (smul_add (Int.triangularSign n) (c₁ ≫ π) (c₂ ≫ π))) }
  exact AddCommGrpCat.ofHom F

private lemma homZeroSourceCycleComponent_boundary (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0)
    (x : ((homCochainComplex P Q).sc n).X₁) (p : ℤ) :
    homZeroSourceCycleComponent P Q n hZero
        (((homCochainComplex P Q).sc n).toCycles x) p ≫ Q.homologyπ (n - p) = 0 := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let S : ShortComplex AddCommGrpCat.{v} := H.sc n
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q (n - 1))
  let B : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n)
  have hPrev : (ComplexShape.up ℤ).prev n = n - 1 :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1) n (by omega))
  have hNext : (ComplexShape.up ℤ).next n = n + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl)
  let e : S ≅ H.sc' (n - 1) n (n + 1) := H.isoSc' (n - 1) n (n + 1) hPrev hNext
  let a : S.X₁ ⟶ A := e.hom.τ₁
  let m : B ⟶ B := e.hom.τ₂
  let d : A ⟶ B := H.d (n - 1) n
  have hm : m = 𝟙 B := rfl
  have hD : a ≫ d = S.f :=
    e.hom.comm₁₂.trans
      ((congrArg (fun t : B ⟶ B => S.f ≫ t) hm).trans (Category.comp_id S.f))
  let t : S.X₁ ⟶ H.cycles n := S.toCycles
  let ι : H.cycles n ⟶ B := H.iCycles n
  have hT : t ≫ ι = S.f := S.toCycles_i
  let x₀ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q (n - 1) := a.hom x
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n := ι.hom (t.hom x)
  have hx : γ = d.hom x₀ :=
    (AddCommGrpCat.comp_apply t ι x).symm.trans
      ((ConcreteCategory.congr_hom hT x).trans
        ((ConcreteCategory.congr_hom hD.symm x).trans (AddCommGrpCat.comp_apply a d x)))
  let b : P.X p ⟶ Q.X (n - 1 - p) :=
    n.negOnePow • homCochainComponent P Q (n - 1) x₀ p
  have hb : homCochainComponent P Q n γ p = b ≫ Q.d (n - 1 - p) (n - p) :=
    (congrArg (fun z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n =>
        homCochainComponent P Q n z p) hx).trans
      ((homCochainComponent_d P Q hZero (n - 1) n (by omega) x₀ p).trans
        (Linear.units_smul_comp n.negOnePow
          (homCochainComponent P Q (n - 1) x₀ p) (Q.d (n - 1 - p) (n - p))).symm)
  have hj : (ComplexShape.up ℤ).next (n - p) = n - p + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n - p) (n - p + 1) rfl)
  unfold homZeroSourceCycleComponent
  exact Q.liftCycles_homologyπ_eq_zero_of_boundary (i := n - p)
    (homCochainComponent P Q n γ p) (n - p + 1) hj b hb

/-- Hom boundaries vanish under the canonical cycle-product map. -/
lemma toCycles_homZeroSourceCycleMap (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) :
    ((homCochainComplex P Q).sc n).toCycles ≫ homZeroSourceCycleMap P Q n hZero = 0 := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let S : ShortComplex AddCommGrpCat.{v} := H.sc n
  let B : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p))
  let t : S.X₁ ⟶ H.cycles n := S.toCycles
  let c : H.cycles n ⟶ B := homZeroSourceCycleMap P Q n hZero
  apply AddCommGrpCat.ext
  intro x
  funext p
  have h : ((t ≫ c).hom x) p = (c.hom (t.hom x)) p :=
    congrFun (AddCommGrpCat.comp_apply t c x) p
  change ((t ≫ c).hom x) p = 0
  have hb : (c.hom (t.hom x)) p = 0 := by
    change Int.triangularSign n •
      (homZeroSourceCycleComponent P Q n hZero (t.hom x) p ≫
        Q.homologyπ (n - p)) = 0
    exact (congrArg (fun a : P.X p ⟶ Q.homology (n - p) =>
      Int.triangularSign n • a)
        (homZeroSourceCycleComponent_boundary P Q n hZero x p)).trans
          (smul_zero (Int.triangularSign n))
  exact h.trans hb

/-- The canonical full-product cohomology comparison, before any projectivity assumption. -/
def homZeroSourceCohomologyComparison (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) :
    (homCochainComplex P Q).homology n ⟶
      AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) :=
  ((homCochainComplex P Q).sc n).homologyIsCokernel.desc
    (CokernelCofork.ofπ (homZeroSourceCycleMap P Q n hZero)
      (toCycles_homZeroSourceCycleMap P Q n hZero))

/-- The comparison descends the cycle map. -/
@[reassoc]
lemma homologyπ_homZeroSourceCohomologyComparison (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) :
    (homCochainComplex P Q).homologyπ n ≫ homZeroSourceCohomologyComparison P Q n hZero =
      homZeroSourceCycleMap P Q n hZero := by
  exact Cofork.IsColimit.π_desc ((homCochainComplex P Q).sc n).homologyIsCokernel

/-- Every representative retains its triangular sign and Q-homology component. -/
lemma homZeroSourceCohomologyComparison_apply (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0)
    (z : (homCochainComplex P Q).cycles n) (p : ℤ) :
    homZeroSourceCohomologyComparison P Q n hZero
        ((homCochainComplex P Q).homologyπ n z) p =
      Int.triangularSign n •
        (homZeroSourceCycleComponent P Q n hZero z p ≫ Q.homologyπ (n - p)) := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let B : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p))
  let π : H.cycles n ⟶ H.homology n := H.homologyπ n
  let c : H.homology n ⟶ B := homZeroSourceCohomologyComparison P Q n hZero
  let m : H.cycles n ⟶ B := homZeroSourceCycleMap P Q n hZero
  have h : π ≫ c = m := homologyπ_homZeroSourceCohomologyComparison P Q n hZero
  have hp : c.hom (π.hom z) = m.hom z :=
    (AddCommGrpCat.comp_apply π c z).symm.trans (ConcreteCategory.congr_hom h z)
  exact (congrFun hp p).trans (by rfl)

/-- The source and target maps act on the whole Q-homology product. -/
def homCohomologyProductMap {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ) :
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) ⟶
      AddCommGrpCat.of (∀ p : ℤ, P'.X p ⟶ Q'.homology (n - p)) :=
  AddCommGrpCat.ofHom
    { toFun k p := f.f p ≫ k p ≫ HomologicalComplex.homologyMap g (n - p)
      map_zero' := by
        funext p
        simp only [Pi.zero_apply, CategoryTheory.Limits.comp_zero,
          CategoryTheory.Limits.zero_comp]
      map_add' k k' := by
        funext p
        simp only [Pi.add_apply, Preadditive.comp_add, Preadditive.add_comp] }

/-- Simultaneous naturality is a square of the cohomology and full-product maps. -/
lemma homZeroSourceCohomologyComparison_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (hZero' : ∀ i j : ℤ, P'.d i j = 0) :
    HomologicalComplex.homologyMap (homCochainComplexMap f g) n ≫
        homZeroSourceCohomologyComparison P' Q' n hZero' =
      homZeroSourceCohomologyComparison P Q n hZero ≫ homCohomologyProductMap f g n := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let H' : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P' Q'
  let B : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p))
  let B' : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P'.X p ⟶ Q'.homology (n - p))
  let a : H ⟶ H' := homCochainComplexMap f g
  let l : H.cycles n ⟶ H'.cycles n := HomologicalComplex.cyclesMap a n
  let κ : H.homology n ⟶ H'.homology n := HomologicalComplex.homologyMap a n
  let π : H.cycles n ⟶ H.homology n := H.homologyπ n
  let π' : H'.cycles n ⟶ H'.homology n := H'.homologyπ n
  let c : H.homology n ⟶ B := homZeroSourceCohomologyComparison P Q n hZero
  let c' : H'.homology n ⟶ B' := homZeroSourceCohomologyComparison P' Q' n hZero'
  let m : H.cycles n ⟶ B := homZeroSourceCycleMap P Q n hZero
  let m' : H'.cycles n ⟶ B' := homZeroSourceCycleMap P' Q' n hZero'
  let μ : B ⟶ B' := homCohomologyProductMap f g n
  have hm : l ≫ m' = m ≫ μ := by
    apply AddCommGrpCat.ext
    intro z
    funext p
    let t : P'.X p ⟶ P.X p := f.f p
    let b : P.X p ⟶ Q.cycles (n - p) :=
      homZeroSourceCycleComponent P Q n hZero z p
    let b' : P'.X p ⟶ Q'.cycles (n - p) :=
      homZeroSourceCycleComponent P' Q' n hZero' (l.hom z) p
    let πQ : Q.cycles (n - p) ⟶ Q.homology (n - p) := Q.homologyπ (n - p)
    let πQ' : Q'.cycles (n - p) ⟶ Q'.homology (n - p) := Q'.homologyπ (n - p)
    let s : Q.cycles (n - p) ⟶ Q'.cycles (n - p) :=
      HomologicalComplex.cyclesMap g (n - p)
    let v : Q.homology (n - p) ⟶ Q'.homology (n - p) :=
      HomologicalComplex.homologyMap g (n - p)
    let k : P.X p ⟶ Q.homology (n - p) := b ≫ πQ
    have hb : b' = t ≫ b ≫ s :=
      homZeroSourceCycleComponent_naturality f g n p hZero hZero' z
    have hQ : s ≫ πQ' = πQ ≫ v :=
      (HomologicalComplex.homologyπ_naturality g (n - p)).symm
    have hPoint : b' ≫ πQ' = t ≫ k ≫ v :=
      (congrArg (fun e : P'.X p ⟶ Q'.cycles (n - p) => e ≫ πQ') hb).trans
        ((Category.assoc t (b ≫ s) πQ').trans
          (congrArg (fun e : P.X p ⟶ Q'.homology (n - p) => t ≫ e)
            ((Category.assoc b s πQ').trans
              ((congrArg (fun e : Q.cycles (n - p) ⟶ Q'.homology (n - p) =>
                b ≫ e) hQ).trans (Category.assoc b πQ v).symm))))
    have hSigned : Int.triangularSign n • (b' ≫ πQ') =
        t ≫ (Int.triangularSign n • k) ≫ v :=
      (congrArg (fun e : P'.X p ⟶ Q'.homology (n - p) =>
        Int.triangularSign n • e) hPoint).trans
        ((Linear.comp_units_smul t (Int.triangularSign n) (k ≫ v)).symm.trans
          (congrArg (fun e : P.X p ⟶ Q'.homology (n - p) => t ≫ e)
            (Linear.units_smul_comp (Int.triangularSign n) k v).symm))
    have hLeft : ((l ≫ m').hom z) p = Int.triangularSign n • (b' ≫ πQ') :=
      (congrFun (AddCommGrpCat.comp_apply l m' z) p).trans (by rfl)
    have hRight : ((m ≫ μ).hom z) p = t ≫ (Int.triangularSign n • k) ≫ v :=
      (congrFun (AddCommGrpCat.comp_apply m μ z) p).trans (by rfl)
    exact hLeft.trans (hSigned.trans hRight.symm)
  have hπ : π ≫ c = m := homologyπ_homZeroSourceCohomologyComparison P Q n hZero
  have hπ' : π' ≫ c' = m' :=
    homologyπ_homZeroSourceCohomologyComparison P' Q' n hZero'
  have hκ : π ≫ κ = l ≫ π' := HomologicalComplex.homologyπ_naturality a n
  apply (cancel_epi π).1
  change π ≫ (κ ≫ c') = π ≫ (c ≫ μ)
  calc
    _ = (π ≫ κ) ≫ c' := (Category.assoc π κ c').symm
    _ = (l ≫ π') ≫ c' := congrArg (fun t => t ≫ c') hκ
    _ = l ≫ (π' ≫ c') := Category.assoc l π' c'
    _ = l ≫ m' := congrArg (fun t => l ≫ t) hπ'
    _ = m ≫ μ := hm
    _ = (π ≫ c) ≫ μ := congrArg (fun t => t ≫ μ) hπ.symm
    _ = π ≫ (c ≫ μ) := Category.assoc π c μ

private lemma projectiveHom_preservesHomology (X : C) [Projective X] :
    (preadditiveCoyoneda.obj (op X)).PreservesHomology := by
  let U := forget₂ (ModuleCat.{v} (End X)ᵐᵒᵖ) AddCommGrpCat.{v}
  letI : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
  change (preadditiveCoyonedaObj X ⋙ U).PreservesHomology
  infer_instance

/-- Projective Hom and the adjacent-degree comparison compute the Q row homology. -/
def homZeroSourceRowCohomologyIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (hP : Projective (P.X p)) :
    (homZeroSourceRow P Q n p).homology ≅
      AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p)) := by
  letI : Projective (P.X p) := hP
  let F : C ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op (P.X p))
  let S : ShortComplex C := Q.sc' (n - 1 - p) (n - p) (n + 1 - p)
  letI : F.PreservesHomology := by
    let U := forget₂ (ModuleCat.{v} (End (P.X p))ᵐᵒᵖ) AddCommGrpCat.{v}
    letI : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
    change (preadditiveCoyonedaObj (P.X p) ⋙ U).PreservesHomology
    infer_instance
  have hprev : (ComplexShape.up ℤ).prev (n - p) = n - 1 - p :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1 - p) (n - p) (by omega))
  have hnext : (ComplexShape.up ℤ).next (n - p) = n + 1 - p :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n - p) (n + 1 - p) (by omega))
  let e : Q.homology (n - p) ≅ S.homology :=
    Q.homologyIsoSc' (n - 1 - p) (n - p) (n + 1 - p) hprev hnext
  exact S.mapHomologyIso F ≪≫ F.mapIso e.symm

/-- A row representative is the Q-cycle morphism followed by the homology quotient. -/
lemma homZeroSourceRowCohomologyIso_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (hP : Projective (P.X p))
    (z : (homZeroSourceRow P Q n p).cycles) (k : P.X p ⟶ Q.cycles (n - p))
    (hk : (homZeroSourceRow P Q n p).iCycles z = k ≫ Q.iCycles (n - p)) :
    (homZeroSourceRowCohomologyIso P Q n p hP).hom
        ((homZeroSourceRow P Q n p).homologyπ z) = k ≫ Q.homologyπ (n - p) := by
  letI : Projective (P.X p) := hP
  let F : C ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op (P.X p))
  let S : ShortComplex C := Q.sc' (n - 1 - p) (n - p) (n + 1 - p)
  letI : F.PreservesHomology := by
    let U := forget₂ (ModuleCat.{v} (End (P.X p))ᵐᵒᵖ) AddCommGrpCat.{v}
    letI : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
    change (preadditiveCoyonedaObj (P.X p) ⋙ U).PreservesHomology
    infer_instance
  have hprev : (ComplexShape.up ℤ).prev (n - p) = n - 1 - p :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1 - p) (n - p) (by omega))
  have hnext : (ComplexShape.up ℤ).next (n - p) = n + 1 - p :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n - p) (n + 1 - p) (by omega))
  let e : Q.homology (n - p) ≅ S.homology :=
    Q.homologyIsoSc' (n - 1 - p) (n - p) (n + 1 - p) hprev hnext
  let c : Q.cycles (n - p) ≅ S.cycles :=
    Q.cyclesIsoSc' (n - 1 - p) (n - p) (n + 1 - p) hprev hnext
  let z₀ : (S.map F).cycles := by
    let z₁ := z
    dsimp only [homZeroSourceRow] at z₁
    exact z₁
  have hk₀ : (S.map F).iCycles z₀ = k ≫ Q.iCycles (n - p) := by
    change (S.map F).iCycles z₀ = k ≫ Q.iCycles (n - p) at hk
    exact hk
  let E₀ := homZeroSourceRowCohomologyIso P Q n p hP
  change (S.map F).homology ≅ F.obj (Q.homology (n - p)) at E₀
  have hPack : E₀ = S.mapHomologyIso F ≪≫ F.mapIso e.symm := rfl
  let π : (S.map F).cycles ⟶ (S.map F).homology := (S.map F).homologyπ
  let H : (S.map F).homology ⟶ F.obj S.homology := (S.mapHomologyIso F).hom
  let C₀ : (S.map F).cycles ⟶ F.obj S.cycles := (S.mapCyclesIso F).hom
  let T : F.obj S.cycles ⟶ F.obj S.homology := F.map S.homologyπ
  have hπ : π ≫ H = C₀ ≫ T := by
    let h : S.LeftHomologyData := S.homologyData.left
    let H₀ : (S.map F).homology ≅ F.obj h.H := (h.map F).homologyIso
    let K₀ : (S.map F).cycles ≅ F.obj h.K := (h.map F).cyclesIso
    let mπ : F.obj h.K ⟶ F.obj h.H := F.map h.π
    let hInv : F.obj h.H ⟶ F.obj S.homology := F.map h.homologyIso.inv
    let cInv : F.obj h.K ⟶ F.obj S.cycles := F.map h.cyclesIso.inv
    have hmπ : (h.map F).π = mπ := rfl
    have h₁ : π ≫ H₀.hom = K₀.hom ≫ mπ := by
      have w := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
        (S := S.map F) (h.map F)
      change π ≫ H₀.hom = K₀.hom ≫ (h.map F).π at w
      exact w.trans (congrArg (fun a : F.obj h.K ⟶ F.obj h.H => K₀.hom ≫ a) hmπ)
    have hH : H = H₀.hom ≫ hInv := by
      have w := congrArg (fun a : (S.map F).homology ≅ F.obj S.homology => a.hom)
        (h.mapHomologyIso_eq F)
      change H = H₀.hom ≫ hInv at w
      exact w
    have hC : C₀ = K₀.hom ≫ cInv := by
      have w := congrArg (fun a : (S.map F).cycles ≅ F.obj S.cycles => a.hom)
        (h.mapCyclesIso_eq F)
      change C₀ = K₀.hom ≫ cInv at w
      exact w
    have hF : mπ ≫ hInv = cInv ≫ T := by
      have w := congrArg F.map
        (ShortComplex.LeftHomologyData.π_comp_homologyIso_inv (S := S) h)
      change F.map (h.π ≫ h.homologyIso.inv) =
        F.map (h.cyclesIso.inv ≫ S.homologyπ) at w
      exact (F.map_comp h.π h.homologyIso.inv).symm.trans
        (w.trans (F.map_comp h.cyclesIso.inv S.homologyπ))
    calc
      π ≫ H = π ≫ (H₀.hom ≫ hInv) := congrArg (fun a => π ≫ a) hH
      _ = (π ≫ H₀.hom) ≫ hInv := (Category.assoc π H₀.hom hInv).symm
      _ = (K₀.hom ≫ mπ) ≫ hInv := congrArg (fun a => a ≫ hInv) h₁
      _ = K₀.hom ≫ (mπ ≫ hInv) := Category.assoc K₀.hom mπ hInv
      _ = K₀.hom ≫ (cInv ≫ T) := congrArg (fun a => K₀.hom ≫ a) hF
      _ = (K₀.hom ≫ cInv) ≫ T := (Category.assoc K₀.hom cInv T).symm
      _ = C₀ ≫ T := congrArg (fun a => a ≫ T) hC.symm
  have he : S.homologyπ ≫ e.inv = c.inv ≫ Q.homologyπ (n - p) :=
    Q.π_homologyIsoSc'_inv (n - 1 - p) (n - p) (n + 1 - p) hprev hnext
  let x : F.obj S.cycles := C₀.hom z₀
  let x₀ : P.X p ⟶ S.cycles := x
  let y : P.X p ⟶ S.X₂ := (S.map F).iCycles.hom z₀
  let I : F.obj S.cycles ⟶ F.obj S.X₂ := F.map S.iCycles
  have hI : I.hom x = x₀ ≫ S.iCycles := rfl
  have hi : x₀ ≫ S.iCycles = y :=
    hI.symm.trans ((AddCommGrpCat.comp_apply C₀ I z₀).symm.trans
      (ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F) z₀))
  have hy : y = k ≫ Q.iCycles (n - p) := hk₀
  have ha : x₀ ≫ c.inv = k := by
    apply (cancel_mono (Q.iCycles (n - p))).1
    change (x₀ ≫ c.inv) ≫ Q.iCycles (n - p) = k ≫ Q.iCycles (n - p)
    exact (Category.assoc x₀ c.inv (Q.iCycles (n - p))).trans
      ((congrArg (fun a : S.cycles ⟶ Q.X (n - p) => x₀ ≫ a)
        (Q.cyclesIsoSc'_inv_iCycles (n - 1 - p) (n - p) (n + 1 - p) hprev hnext)).trans
          (hi.trans hy))
  let v : P.X p ⟶ S.homology := H.hom (π.hom z₀)
  have hT : T.hom x = x₀ ≫ S.homologyπ := rfl
  have hv : v = x₀ ≫ S.homologyπ :=
    (AddCommGrpCat.comp_apply π H z₀).symm.trans
      ((ConcreteCategory.congr_hom hπ z₀).trans
        ((AddCommGrpCat.comp_apply C₀ T z₀).trans hT))
  let R : F.obj S.homology ⟶ F.obj (Q.homology (n - p)) := F.map e.inv
  have hE : E₀.hom = H ≫ R := by
    have w := congrArg (fun a : (S.map F).homology ≅ F.obj (Q.homology (n - p)) => a.hom)
      hPack
    change E₀.hom = H ≫ R at w
    exact w
  have hValue : E₀.hom.hom (π.hom z₀) = R.hom v :=
    (congrArg (fun a : (S.map F).homology ⟶ F.obj (Q.homology (n - p)) =>
      a.hom (π.hom z₀)) hE).trans (AddCommGrpCat.comp_apply H R (π.hom z₀))
  have hR : R.hom v = v ≫ e.inv := rfl
  have hRegular : v ≫ e.inv = k ≫ Q.homologyπ (n - p) :=
    (congrArg (fun a : P.X p ⟶ S.homology => a ≫ e.inv) hv).trans
      ((Category.assoc x₀ S.homologyπ e.inv).trans
        ((congrArg (fun a : S.cycles ⟶ Q.homology (n - p) => x₀ ≫ a) he).trans
          ((Category.assoc x₀ c.inv (Q.homologyπ (n - p))).symm.trans
            (congrArg (fun a : P.X p ⟶ Q.cycles (n - p) => a ≫ Q.homologyπ (n - p)) ha))))
  change E₀.hom.hom (π.hom z₀) = k ≫ Q.homologyπ (n - p)
  exact hValue.trans (hR.trans hRegular)

/-- Projective terms give the pointwise Q-homology comparison of the entire row diagram. -/
def homZeroSourceRowCohomologyDiagramIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hProj : ∀ p : ℤ, Projective (P.X p)) :
    homZeroSourceRows P Q n ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{v} ≅
      Discrete.functor (fun p : ℤ => AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p))) :=
  Discrete.natIso (fun p => homZeroSourceRowCohomologyIso P Q n p.as (hProj p.as))

/-- Exact products and projective Hom compute the cohomology of full-product Hom. -/
def homZeroSourceCohomologyIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (hProj : ∀ p : ℤ, Projective (P.X p)) :
    (homCochainComplex P Q).homology n ≅
      AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) := by
  let K := CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) Q
  let R := homZeroSourceRows P Q n
  let T := Discrete.functor (fun p : ℤ => AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p)))
  exact HomologicalComplex.homologyMapIso (homCochainComplexIso P Q) n ≪≫
    ShortComplex.homologyMapIso (K.isoSc' (n - 1) n (n + 1)
      ((ComplexShape.up ℤ).prev_eq'
        (ComplexShape.up_mk (n - 1) n (by omega)))
      ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl))) ≪≫
    ShortComplex.homologyMapIso (rawHomZeroSourceShortComplexIso P Q n hZero) ≪≫
    ShortComplex.homologyLimitIso R ≪≫
    (lim (J := Discrete ℤ) (C := AddCommGrpCat.{v})).mapIso
      (homZeroSourceRowCohomologyDiagramIso P Q n hProj) ≪≫ AddCommGrpCat.intLimitIsoPi T

/-- Each component of the cohomology isomorphism is the row homology projection. -/
lemma homZeroSourceCohomologyIso_hom_eval (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (hProj : ∀ p : ℤ, Projective (P.X p))
    (p : ℤ) :
    (homZeroSourceCohomologyIso P Q n hZero hProj).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
          (fun p : ℤ => P.X p ⟶ Q.homology (n - p)) p) =
      HomologicalComplex.homologyMap (homCochainComplexIso P Q).hom n ≫
        ShortComplex.homologyMap
          (HomologicalComplex.isoSc'
            (CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) Q)
            (n - 1) n (n + 1)
            ((ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1) n (by omega)))
            ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl))).hom ≫
        ShortComplex.homologyMap (rawHomZeroSourceProjection P Q n hZero p) ≫
        (homZeroSourceRowCohomologyIso P Q n p (hProj p)).hom := by
  let K := CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) Q
  let R := homZeroSourceRows P Q n
  let T := Discrete.functor (fun p : ℤ => AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p)))
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1) n (by omega))
  have hnext : (ComplexShape.up ℤ).next n = n + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl)
  let a := HomologicalComplex.homologyMapIso (homCochainComplexIso P Q) n
  let b := ShortComplex.homologyMapIso (K.isoSc' (n - 1) n (n + 1) hprev hnext)
  let c := ShortComplex.homologyMapIso (rawHomZeroSourceShortComplexIso P Q n hZero)
  let d := ShortComplex.homologyLimitIso R
  let e := (lim (J := Discrete ℤ) (C := AddCommGrpCat.{v})).mapIso
    (homZeroSourceRowCohomologyDiagramIso P Q n hProj)
  let t := AddCommGrpCat.intLimitIsoPi T
  let E := homZeroSourceCohomologyIso P Q n hZero hProj
  have hPack : E = a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ t := rfl
  have hPackHom : E.hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ t.hom := by
    rw [hPack]
    rfl
  let V : AddCommGrpCat.{v} := AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p))
  let v : AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p)) ⟶ V :=
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
      (fun p : ℤ => P.X p ⟶ Q.homology (n - p)) p)
  let πT : limit T ⟶ V := limit.π T ⟨p⟩
  let πR : limit (R ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{v}) ⟶
      (R.obj ⟨p⟩).homology :=
    limit.π (R ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{v}) ⟨p⟩
  let row : (R.obj ⟨p⟩).homology ⟶ V :=
    (homZeroSourceRowCohomologyIso P Q n p (hProj p)).hom
  let q : (ShortComplex.limitShortComplex R).homology ⟶ (R.obj ⟨p⟩).homology :=
    ShortComplex.homologyMap (ShortComplex.limitShortComplexProjection R ⟨p⟩)
  let q₀ : (K.sc' (n - 1) n (n + 1)).homology ⟶ (R.obj ⟨p⟩).homology :=
    ShortComplex.homologyMap (rawHomZeroSourceProjection P Q n hZero p)
  have ht : t.hom ≫ v = πT := AddCommGrpCat.intLimitIsoPi_hom_eval T p
  have he : e.hom ≫ πT = πR ≫ row := by
    dsimp only [e, Functor.mapIso]
    exact limit.map_π (homZeroSourceRowCohomologyDiagramIso P Q n hProj).hom ⟨p⟩
  have hd : d.hom ≫ πR = q := ShortComplex.homologyLimitIso_hom_π R ⟨p⟩
  have hc : c.hom ≫ q = q₀ :=
    (ShortComplex.homologyMap_comp (rawHomZeroSourceShortComplexIso P Q n hZero).hom
      (ShortComplex.limitShortComplexProjection R ⟨p⟩)).symm.trans
        (congrArg
          (fun f : K.sc' (n - 1) n (n + 1) ⟶ R.obj ⟨p⟩ =>
            (ShortComplex.homologyMap f : (K.sc' (n - 1) n (n + 1)).homology ⟶
              (R.obj ⟨p⟩).homology))
          (rawHomZeroSourceShortComplexIso_hom_projection P Q n hZero p))
  have hPacked : E.hom ≫ v =
      (a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ t.hom) ≫ v :=
    congrArg (fun f => f ≫ v) hPackHom
  have hProjection : E.hom ≫ v = a.hom ≫ b.hom ≫ q₀ ≫ row := by
    calc
      E.hom ≫ v =
          (a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ t.hom) ≫ v := hPacked
      _ = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ (t.hom ≫ v) := by
        let A := a.hom
        let B := b.hom
        let C₀ := c.hom
        let D := d.hom
        let F := e.hom
        let G := t.hom
        have h₀ := Category.assoc A (B ≫ C₀ ≫ D ≫ F ≫ G) v
        have h₁ := Category.assoc B (C₀ ≫ D ≫ F ≫ G) v
        have h₂ := Category.assoc C₀ (D ≫ F ≫ G) v
        have h₃ := Category.assoc D (F ≫ G) v
        have h₄ := Category.assoc F G v
        exact h₀.trans
          (congrArg (fun f => A ≫ f) (h₁.trans
            (congrArg (fun f => B ≫ f) (h₂.trans
              (congrArg (fun f => C₀ ≫ f) (h₃.trans
                (congrArg (fun f => D ≫ f) h₄)))))))
      _ = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ πT :=
        congrArg (fun f => a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom ≫ f) ht
      _ = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ (πR ≫ row) :=
        congrArg (fun f => a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ f) he
      _ = a.hom ≫ b.hom ≫ c.hom ≫ (d.hom ≫ πR) ≫ row := by
        simp only [Category.assoc]
      _ = a.hom ≫ b.hom ≫ c.hom ≫ q ≫ row :=
        congrArg (fun f => a.hom ≫ b.hom ≫ c.hom ≫ f ≫ row) hd
      _ = a.hom ≫ b.hom ≫ (c.hom ≫ q) ≫ row := by
        simp only [Category.assoc]
      _ = a.hom ≫ b.hom ≫ q₀ ≫ row :=
        congrArg (fun f => a.hom ≫ b.hom ≫ f ≫ row) hc
  exact hProjection

/-- The full-product isomorphism retains every cycle representative and triangular sign. -/
lemma homZeroSourceCohomologyIso_apply (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (hProj : ∀ p : ℤ, Projective (P.X p))
    (z : (homCochainComplex P Q).cycles n) (p : ℤ) :
    (homZeroSourceCohomologyIso P Q n hZero hProj).hom
        ((homCochainComplex P Q).homologyπ n z) p =
      Int.triangularSign n •
        (homZeroSourceCycleComponent P Q n hZero z p ≫ Q.homologyπ (n - p)) := by
  let H : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex P Q
  let K : CochainComplex AddCommGrpCat.{v} ℤ :=
    CochainComplex.HomComplex ((cochainComplexEquivalence C).functor.obj P) Q
  let L : ShortComplex AddCommGrpCat.{v} := K.sc' (n - 1) n (n + 1)
  let R : ShortComplex AddCommGrpCat.{v} := homZeroSourceRow P Q n p
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n)
  let B : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (n - p))
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of (P.X p ⟶ Q.homology (n - p))
  let a : H ⟶ K := (homCochainComplexIso P Q).hom
  let b : K.sc n ⟶ L := (K.isoSc' (n - 1) n (n + 1)
      ((ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (n - 1) n (by omega)))
      ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl))).hom
  let t : L ⟶ R := rawHomZeroSourceProjection P Q n hZero p
  let ca : H.cycles n ⟶ K.cycles n := HomologicalComplex.cyclesMap a n
  let cb : K.cycles n ⟶ L.cycles := ShortComplex.cyclesMap b
  let ct : L.cycles ⟶ R.cycles := ShortComplex.cyclesMap t
  let z₁ : K.cycles n := ca.hom z
  let z₂ : L.cycles := cb.hom z₁
  let z₃ : R.cycles := ct.hom z₂
  let πH : H.cycles n ⟶ H.homology n := H.homologyπ n
  let πK : K.cycles n ⟶ K.homology n := K.homologyπ n
  let πL : L.cycles ⟶ L.homology := L.homologyπ
  let πR : R.cycles ⟶ R.homology := R.homologyπ
  let ha : H.homology n ⟶ K.homology n := HomologicalComplex.homologyMap a n
  let hb : K.homology n ⟶ L.homology := ShortComplex.homologyMap b
  let ht : L.homology ⟶ R.homology := ShortComplex.homologyMap t
  let E : H.homology n ≅ B := homZeroSourceCohomologyIso P Q n hZero hProj
  let e : R.homology ≅ G := homZeroSourceRowCohomologyIso P Q n p (hProj p)
  let ev : B ⟶ G := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun p : ℤ => P.X p ⟶ Q.homology (n - p)) p)
  have hπA : πH ≫ ha = ca ≫ πK := HomologicalComplex.homologyπ_naturality a n
  have hπB : πK ≫ hb = cb ≫ πL := ShortComplex.homologyπ_naturality b
  have hπT : πL ≫ ht = ct ≫ πR := ShortComplex.homologyπ_naturality t
  have hA : ha.hom (πH.hom z) = πK.hom z₁ :=
    (AddCommGrpCat.comp_apply πH ha z).symm.trans
      ((ConcreteCategory.congr_hom hπA z).trans (AddCommGrpCat.comp_apply ca πK z))
  have hB : hb.hom (πK.hom z₁) = πL.hom z₂ :=
    (AddCommGrpCat.comp_apply πK hb z₁).symm.trans
      ((ConcreteCategory.congr_hom hπB z₁).trans (AddCommGrpCat.comp_apply cb πL z₁))
  have hT : ht.hom (πL.hom z₂) = πR.hom z₃ :=
    (AddCommGrpCat.comp_apply πL ht z₂).symm.trans
      ((ConcreteCategory.congr_hom hπT z₂).trans (AddCommGrpCat.comp_apply ct πR z₂))
  have hEval : E.hom ≫ ev = ha ≫ hb ≫ ht ≫ e.hom :=
    homZeroSourceCohomologyIso_hom_eval P Q n hZero hProj p
  let r₁ : K.homology n ⟶ G := hb ≫ ht ≫ e.hom
  let r₂ : L.homology ⟶ G := ht ≫ e.hom
  have hEvalValue (x : B) : ev.hom x = x p := rfl
  have hv : E.hom.hom (πH.hom z) p = e.hom.hom (πR.hom z₃) := by
    have hLeft : E.hom.hom (πH.hom z) p = (E.hom ≫ ev).hom (πH.hom z) :=
      (hEvalValue (E.hom.hom (πH.hom z))).symm.trans
        (AddCommGrpCat.comp_apply E.hom ev (πH.hom z)).symm
    have hPoint : (E.hom ≫ ev).hom (πH.hom z) =
        (ha ≫ r₁).hom (πH.hom z) := ConcreteCategory.congr_hom hEval (πH.hom z)
    have hRight : (ha ≫ r₁).hom (πH.hom z) = e.hom.hom (πR.hom z₃) :=
      (AddCommGrpCat.comp_apply ha r₁ (πH.hom z)).trans
        ((congrArg r₁.hom hA).trans
          ((AddCommGrpCat.comp_apply hb r₂ (πK.hom z₁)).trans
            ((congrArg r₂.hom hB).trans
              ((AddCommGrpCat.comp_apply ht e.hom (πL.hom z₂)).trans
                (congrArg e.hom.hom hT)))))
    exact hLeft.trans (hPoint.trans hRight)
  let ιH : H.cycles n ⟶ A := H.iCycles n
  let ιK : K.cycles n ⟶ A := K.iCycles n
  let ιL : L.cycles ⟶ L.X₂ := L.iCycles
  let ιR : R.cycles ⟶ R.X₂ := R.iCycles
  let m : A ⟶ A := a.f n
  let γ : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence C).functor.obj P) Q n := ιH.hom z
  have hCycleT : ct ≫ ιR = ιL ≫ t.τ₂ := ShortComplex.cyclesMap_i t
  have hCycleB : cb ≫ ιL = ιK := by
    have w : cb ≫ ιL = ιK ≫ b.τ₂ := ShortComplex.cyclesMap_i b
    have hτ : b.τ₂ = 𝟙 A := rfl
    exact w.trans ((congrArg (fun a : A ⟶ A => ιK ≫ a) hτ).trans
      (Category.comp_id ιK))
  have hCycleA : ca ≫ ιK = ιH ≫ m := HomologicalComplex.cyclesMap_i a n
  have hγ : m.hom γ = Int.triangularSign n • γ := rfl
  have hL : ιR.hom z₃ = t.τ₂.hom (ιL.hom z₂) :=
    (AddCommGrpCat.comp_apply ct ιR z₂).symm.trans
      ((ConcreteCategory.congr_hom hCycleT z₂).trans
        (AddCommGrpCat.comp_apply ιL t.τ₂ z₂))
  have hK : ιL.hom z₂ = ιK.hom z₁ :=
    (AddCommGrpCat.comp_apply cb ιL z₁).symm.trans
      (ConcreteCategory.congr_hom hCycleB z₁)
  have hH : ιK.hom z₁ = Int.triangularSign n • γ :=
    (AddCommGrpCat.comp_apply ca ιK z).symm.trans
      ((ConcreteCategory.congr_hom hCycleA z).trans
        ((AddCommGrpCat.comp_apply ιH m z).trans hγ))
  have hPhysical (η : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
      t.τ₂.hom η = homCochainComponent P Q n η p := rfl
  let κ : P.X p ⟶ Q.cycles (n - p) := homZeroSourceCycleComponent P Q n hZero z p
  have hκ : κ ≫ Q.iCycles (n - p) = homCochainComponent P Q n γ p :=
    homZeroSourceCycleComponent_i P Q n hZero z p
  have hScalar : homCochainComponent P Q n (Int.triangularSign n • γ) p =
      (Int.triangularSign n • κ) ≫ Q.iCycles (n - p) :=
    (homCochainComponent_units_smul P Q n p (Int.triangularSign n) γ).trans
      ((congrArg (fun a : P.X p ⟶ Q.X (n - p) => Int.triangularSign n • a) hκ.symm).trans
        (Linear.units_smul_comp (Int.triangularSign n) κ (Q.iCycles (n - p))).symm)
  have hk : R.iCycles z₃ = (Int.triangularSign n • κ) ≫ Q.iCycles (n - p) :=
    hL.trans ((congrArg t.τ₂.hom hK).trans
      ((congrArg t.τ₂.hom hH).trans ((hPhysical _).trans hScalar)))
  change E.hom.hom (πH.hom z) p =
    Int.triangularSign n • (κ ≫ Q.homologyπ (n - p))
  exact hv.trans ((homZeroSourceRowCohomologyIso_apply P Q n p (hProj p) z₃ _ hk).trans
    (Linear.units_smul_comp (Int.triangularSign n) κ (Q.homologyπ (n - p))))

/-- Exact products identify the computed isomorphism with the canonical cycle comparison. -/
lemma homZeroSourceCohomologyIso_hom (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0) (hProj : ∀ p : ℤ, Projective (P.X p)) :
    (homZeroSourceCohomologyIso P Q n hZero hProj).hom =
      homZeroSourceCohomologyComparison P Q n hZero := by
  apply (cancel_epi ((homCochainComplex P Q).homologyπ n)).1
  apply AddCommGrpCat.ext
  intro z
  funext p
  exact (homZeroSourceCohomologyIso_apply P Q n hZero hProj z p).trans
    (homZeroSourceCohomologyComparison_apply P Q n hZero z p).symm

/-- The canonical comparison is an isomorphism when every source term is projective. -/
lemma isIso_homZeroSourceCohomologyComparison (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hZero : ∀ i j : ℤ, P.d i j = 0)
    (hProj : ∀ p : ℤ, Projective (P.X p)) :
    IsIso (homZeroSourceCohomologyComparison P Q n hZero) := by
  rw [← homZeroSourceCohomologyIso_hom P Q n hZero hProj]
  infer_instance

/-- The computed isomorphism has simultaneous naturality for the P and Q maps. -/
lemma homZeroSourceCohomologyIso_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hZero : ∀ i j : ℤ, P.d i j = 0) (hZero' : ∀ i j : ℤ, P'.d i j = 0)
    (hProj : ∀ p : ℤ, Projective (P.X p)) (hProj' : ∀ p : ℤ, Projective (P'.X p)) :
    HomologicalComplex.homologyMap (homCochainComplexMap f g) n ≫
        (homZeroSourceCohomologyIso P' Q' n hZero' hProj').hom =
      (homZeroSourceCohomologyIso P Q n hZero hProj).hom ≫ homCohomologyProductMap f g n := by
  simpa only [homZeroSourceCohomologyIso_hom] using
    homZeroSourceCohomologyComparison_naturality f g n hZero hZero'

end CohomologyMap

end ChainComplex
