/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.HomCycles
public import MathlibExt.Algebra.Homology.ChainComplex.HomZeroSource
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public meta import Lean.Elab.Tactic.Omega

/-!
# Connecting maps for full-product Hom

The Hom cycles sequence gives a connecting homomorphism whose components
are computed from the differential image and cycle maps. Image projectivity
suffices for the product formula; projective terms are used for the endpoint
cohomology identifications. The target may have nonzero differentials.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma nextDownInt (p : ℤ) : (ComplexShape.down ℤ).next p = p - 1 :=
  (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))

private lemma cyclesEq_iCycles {c : ComplexShape ℤ} (P : HomologicalComplex C c)
    {i j : ℤ} (h : i = j) :
    (eqToHom (congrArg (fun k : ℤ => P.cycles k) h) : P.cycles i ⟶ P.cycles j) ≫
        P.iCycles j = P.iCycles i ≫ (P.XIsoOfEq h).hom := by
  subst j
  simp only [eqToHom_refl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

private lemma toCycles_eq (P : ChainComplex C ℤ) (p : ℤ) {i j : ℤ} (h : i = j) :
    P.toCycles p i ≫
        (eqToHom (congrArg (fun k : ℤ => P.cycles k) h) : P.cycles i ⟶ P.cycles j) =
      P.toCycles p j := by
  subst j
  simp only [eqToHom_refl, Category.comp_id]

private lemma homologyπ_eq (Q : CochainComplex C ℤ) {i j : ℤ} (h : i = j) :
    Q.homologyπ i ≫
        (eqToHom (congrArg (fun k : ℤ => Q.homology k) h) :
          Q.homology i ⟶ Q.homology j) =
      (eqToHom (congrArg (fun k : ℤ => Q.cycles k) h) : Q.cycles i ⟶ Q.cycles j) ≫
        Q.homologyπ j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The outgoing image maps to the cycles one source degree lower. -/
def homCyclesBoundaryComponent (P : ChainComplex C ℤ) (p : ℤ) :
    (outgoingImageZeroComplex P).X p ⟶ (cyclesZeroComplex P).X (p - 1) := by
  let h : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))
  let b : Abelian.image (P.d p ((ComplexShape.down ℤ).next p)) ⟶
      P.cycles ((ComplexShape.down ℤ).next p) :=
    boundaryCyclesMap P p ((ComplexShape.down ℤ).next p)
  let t : P.cycles ((ComplexShape.down ℤ).next p) ⟶ P.cycles (p - 1) :=
    eqToHom (congrArg (fun k : ℤ => P.cycles k) h)
  change Abelian.image (P.d p ((ComplexShape.down ℤ).next p)) ⟶ P.cycles (p - 1)
  exact b ≫ t

/-- Its inclusion is the image inclusion followed by the index equality. -/
@[reassoc]
lemma homCyclesBoundaryComponent_i (P : ChainComplex C ℤ) (p : ℤ) :
    homCyclesBoundaryComponent P p ≫ P.iCycles (p - 1) =
      Abelian.image.ι (P.d p ((ComplexShape.down ℤ).next p)) ≫
        (P.XIsoOfEq ((ComplexShape.down ℤ).next_eq'
          (ComplexShape.down_mk _ _ (by omega)))).hom := by
  let h : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))
  let I := Abelian.image (P.d p ((ComplexShape.down ℤ).next p))
  let b : I ⟶ P.cycles ((ComplexShape.down ℤ).next p) :=
    boundaryCyclesMap P p ((ComplexShape.down ℤ).next p)
  let t : P.cycles ((ComplexShape.down ℤ).next p) ⟶ P.cycles (p - 1) :=
    eqToHom (congrArg (fun k : ℤ => P.cycles k) h)
  let i : P.cycles ((ComplexShape.down ℤ).next p) ⟶ P.X ((ComplexShape.down ℤ).next p) :=
    P.iCycles ((ComplexShape.down ℤ).next p)
  let e : P.X ((ComplexShape.down ℤ).next p) ≅ P.X (p - 1) := P.XIsoOfEq h
  have ht : t ≫ P.iCycles (p - 1) = i ≫ e.hom := cyclesEq_iCycles P h
  have hb : b ≫ i = Abelian.image.ι (P.d p ((ComplexShape.down ℤ).next p)) :=
    boundaryCyclesMap_i P p ((ComplexShape.down ℤ).next p)
  change (b ≫ t) ≫ P.iCycles (p - 1) =
    Abelian.image.ι (P.d p ((ComplexShape.down ℤ).next p)) ≫ e.hom
  exact (Category.assoc b t (P.iCycles (p - 1))).trans
    ((congrArg (fun f : P.cycles ((ComplexShape.down ℤ).next p) ⟶ P.X (p - 1) => b ≫ f)
      ht).trans ((Category.assoc b i e.hom).symm.trans
        (congrArg (fun f : I ⟶ P.X ((ComplexShape.down ℤ).next p) => f ≫ e.hom) hb)))

/-- The image quotient followed by this map is the boundary-to-cycles map. -/
@[reassoc]
lemma quotient_homCyclesBoundaryComponent (P : ChainComplex C ℤ) (p : ℤ) :
    Abelian.factorThruImage (P.d p ((ComplexShape.down ℤ).next p)) ≫
      homCyclesBoundaryComponent P p = P.toCycles p (p - 1) := by
  let h : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))
  let I := Abelian.image (P.d p ((ComplexShape.down ℤ).next p))
  let q : P.X p ⟶ I := Abelian.factorThruImage (P.d p ((ComplexShape.down ℤ).next p))
  let b : I ⟶ P.cycles ((ComplexShape.down ℤ).next p) :=
    boundaryCyclesMap P p ((ComplexShape.down ℤ).next p)
  let t : P.cycles ((ComplexShape.down ℤ).next p) ⟶ P.cycles (p - 1) :=
    eqToHom (congrArg (fun k : ℤ => P.cycles k) h)
  have hb : q ≫ b = P.toCycles p ((ComplexShape.down ℤ).next p) :=
    factorThruImage_boundaryCyclesMap P p ((ComplexShape.down ℤ).next p)
  have ht : P.toCycles p ((ComplexShape.down ℤ).next p) ≫ t = P.toCycles p (p - 1) :=
    toCycles_eq P p h
  change q ≫ (b ≫ t) = P.toCycles p (p - 1)
  exact (Category.assoc q b t).symm.trans
    ((congrArg (fun f : P.X p ⟶ P.cycles ((ComplexShape.down ℤ).next p) => f ≫ t) hb).trans ht)

/-- Boundary precomposition assembles a degree-one map of the full Hom product. -/
def homCyclesBoundaryOperator (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    (homCochainComplex (cyclesZeroComplex P) Q).X n ⟶
      (homCochainComplex (outgoingImageZeroComplex P) Q).X (n + 1) :=
  AddCommGrpCat.ofHom
    ({ toFun z := (homCochainPhysicalPiEquiv (outgoingImageZeroComplex P) Q (n + 1)).symm
        (fun p => homCyclesBoundaryComponent P p ≫
          homCochainComponent (cyclesZeroComplex P) Q n z (p - 1) ≫
            (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom)
       map_zero' := by
         let S : ChainComplex C ℤ := cyclesZeroComplex P
         let T : ChainComplex C ℤ := outgoingImageZeroComplex P
         let E := homCochainPhysicalPiEquiv T Q (n + 1)
         apply E.injective
         have hValues :
             (fun p : ℤ => homCyclesBoundaryComponent P p ≫
               homCochainComponent S Q n 0 (p - 1) ≫
                 (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom) =
             (0 : ∀ p : ℤ, T.X p ⟶ Q.X (n + 1 - p)) := by
           funext p
           let b : T.X p ⟶ S.X (p - 1) := homCyclesBoundaryComponent P p
           let v : S.X (p - 1) ⟶ Q.X (n - (p - 1)) :=
             homCochainComponent S Q n 0 (p - 1)
           let e : Q.X (n - (p - 1)) ⟶ Q.X (n + 1 - p) :=
             (Q.XIsoOfEq (by omega)).hom
           have hv : v = 0 := homCochainComponent_zero S Q n (p - 1)
           change b ≫ v ≫ e = 0
           have hZero : b ≫ (0 : S.X (p - 1) ⟶ Q.X (n - (p - 1))) ≫ e = 0 :=
             (Category.assoc b 0 e).symm.trans
               ((congrArg (fun a : T.X p ⟶ Q.X (n - (p - 1)) => a ≫ e)
                 (Limits.comp_zero (f := b))).trans Limits.zero_comp)
           exact (congrArg (fun a : S.X (p - 1) ⟶ Q.X (n - (p - 1)) => b ≫ a ≫ e)
             hv).trans hZero
         exact (AddEquiv.apply_symm_apply E _).trans (hValues.trans (E.map_zero).symm)
       map_add' z z' := by
         let S : ChainComplex C ℤ := cyclesZeroComplex P
         let T : ChainComplex C ℤ := outgoingImageZeroComplex P
         let E := homCochainPhysicalPiEquiv T Q (n + 1)
         let f (x : CochainComplex.HomComplex.Cochain
             ((cochainComplexEquivalence C).functor.obj S) Q n) (p : ℤ) :=
           homCyclesBoundaryComponent P p ≫ homCochainComponent S Q n x (p - 1) ≫
             (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom
         have hValues : f (z + z') = f z + f z' := by
           funext p
           let b : T.X p ⟶ S.X (p - 1) := homCyclesBoundaryComponent P p
           let v : S.X (p - 1) ⟶ Q.X (n - (p - 1)) :=
             homCochainComponent S Q n z (p - 1)
           let v' : S.X (p - 1) ⟶ Q.X (n - (p - 1)) :=
             homCochainComponent S Q n z' (p - 1)
           let w : S.X (p - 1) ⟶ Q.X (n - (p - 1)) :=
             homCochainComponent S Q n (z + z') (p - 1)
           let e : Q.X (n - (p - 1)) ⟶ Q.X (n + 1 - p) :=
             (Q.XIsoOfEq (by omega)).hom
           have hw : w = v + v' := homCochainComponent_add S Q n (p - 1) z z'
           change b ≫ w ≫ e = b ≫ v ≫ e + b ≫ v' ≫ e
           calc
             _ = (b ≫ w) ≫ e := (Category.assoc b w e).symm
             _ = (b ≫ (v + v')) ≫ e := congrArg (fun a => (b ≫ a) ≫ e) hw
             _ = (b ≫ v + b ≫ v') ≫ e :=
               congrArg (fun a => a ≫ e)
                 (Preadditive.comp_add (T.X p) (S.X (p - 1)) (Q.X (n - (p - 1))) b v v')
             _ = (b ≫ v) ≫ e + (b ≫ v') ≫ e :=
               Preadditive.add_comp (T.X p) (Q.X (n - (p - 1))) (Q.X (n + 1 - p))
                 (b ≫ v) (b ≫ v') e
             _ = _ := congrArg₂ (fun a a' => a + a')
               (Category.assoc b v e) (Category.assoc b v' e)
         apply E.injective
         have hRight : E (E.symm (f z) + E.symm (f z')) = f z + f z' :=
           (E.map_add _ _).trans
             (congrArg₂ (fun a a' => a + a') (E.apply_symm_apply (f z))
               (E.apply_symm_apply (f z')))
         exact (E.apply_symm_apply (f (z + z'))).trans (hValues.trans hRight.symm) } :
      CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n →+
        CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1))

/-- Each physical component keeps the boundary precomposition and target index. -/
lemma homCyclesBoundaryOperator_component (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (z : (homCochainComplex (cyclesZeroComplex P) Q).X n) :
    homCochainComponent (outgoingImageZeroComplex P) Q (n + 1)
        ((homCyclesBoundaryOperator P Q n).hom z) p =
      homCyclesBoundaryComponent P p ≫
        homCochainComponent (cyclesZeroComplex P) Q n z (p - 1) ≫
          (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom :=
  congrFun (AddEquiv.apply_symm_apply
    (homCochainPhysicalPiEquiv (outgoingImageZeroComplex P) Q (n + 1)) _) p

private lemma cochain_v_of_component (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (z : (homCochainComplex P Q).X n) (r q : ℤ) (h : r + n = q) :
    z.v r q h = homCochainComponent P Q n z (-r) ≫
      (Q.XIsoOfEq (by omega : n - (-r) = q)).hom := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let z₀ : CochainComplex.HomComplex.Cochain A Q n := z
  let E := homCochainPhysicalPiEquiv P Q n
  let e : Q.X (n - (-r)) ⟶ Q.X q := (Q.XIsoOfEq (by omega)).hom
  have hv : z₀.v r q h = E z₀ (-r) ≫ e :=
    (congrArg (fun x : CochainComplex.HomComplex.Cochain A Q n => x.v r q h)
      (E.symm_apply_apply z₀)).symm.trans
        (homCochainPhysicalPiEquiv_symm_v P Q n (E z₀) r q h)
  have hc : E z₀ (-r) = homCochainComponent P Q n z₀ (-r) :=
    homCochainPhysicalPiEquiv_apply P Q n (-r) z₀
  exact hv.trans (congrArg (fun a : P.X (-r) ⟶ Q.X (n - (-r)) => a ≫ e) hc)

private lemma inv_XIsoOfEq_d (P : ChainComplex C ℤ) {i i' : ℤ} (h : i = i') (j : ℤ) :
    (P.XIsoOfEq h).inv ≫ P.d i j = P.d i' j := by
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp]

private lemma precomp_component_eq (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n m p : ℤ) (z : (homCochainComplex P Q).X n) {i j : ℤ}
    (h : i = j) (hi : n - i = m - p) (hj : n - j = m - p) :
    P.d p i ≫ homCochainComponent P Q n z i ≫ (Q.XIsoOfEq hi).hom =
      P.d p j ≫ homCochainComponent P Q n z j ≫ (Q.XIsoOfEq hj).hom := by
  subst j
  rfl

/-- The physical Hom differential retains both source and target terms. -/
lemma homCochainComponent_d_general (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m) (z : (homCochainComplex P Q).X n) (p : ℤ) :
    homCochainComponent P Q m (((homCochainComplex P Q).d n m).hom z) p =
      P.d p (p - 1) ≫ homCochainComponent P Q n z (p - 1) ≫
          (Q.XIsoOfEq (by omega : n - (p - 1) = m - p)).hom +
        m.negOnePow • (homCochainComponent P Q n z p ≫ Q.d (n - p) (m - p)) := by
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj P
  let z₀ : CochainComplex.HomComplex.Cochain A Q n := z
  let δz : CochainComplex.HomComplex.Cochain A Q m :=
    ((homCochainComplex P Q).d n m).hom z₀
  let a : P.X p ⟶ A.X (-p) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let d : A.X (-p) ⟶ A.X (-p + 1) := A.d (-p) (-p + 1)
  let v : A.X (-p + 1) ⟶ Q.X (m - p) := z₀.v (-p + 1) (m - p) (by omega)
  let v₀ : A.X (-p) ⟶ Q.X (n - p) := z₀.v (-p) (n - p) (by omega)
  let dQ : Q.X (n - p) ⟶ Q.X (m - p) := Q.d (n - p) (m - p)
  let u : ℤˣ := m.negOnePow
  let r : ℤ := -(-p + 1)
  let e : Q.X (n - r) ⟶ Q.X (m - p) := (Q.XIsoOfEq (by dsimp only [r]; omega)).hom
  let e' : Q.X (n - (p - 1)) ⟶ Q.X (m - p) := (Q.XIsoOfEq (by omega)).hom
  let pre : P.X p ⟶ Q.X (m - p) :=
    P.d p (p - 1) ≫ homCochainComponent P Q n z₀ (p - 1) ≫ e'
  have hRaw : (CochainComplex.HomComplex.δ n m z₀).v (-p) (m - p) (by omega) =
      v₀ ≫ dQ + u • (d ≫ v) :=
    CochainComplex.HomComplex.δ_v n m hnm z₀ (-p) (m - p) (by omega)
      (n - p) (-p + 1) (by omega) rfl
  have hWeighted : u • (v₀ ≫ dQ + u • (d ≫ v)) = u • (v₀ ≫ dQ) + d ≫ v := by
    rw [smul_add, smul_smul, Int.units_mul_self, one_smul]
  have hδ : δz.v (-p) (m - p) (by omega) = u • (v₀ ≫ dQ) + d ≫ v := by
    change (u • CochainComplex.HomComplex.δ n m z₀).v (-p) (m - p) (by omega) = _
    exact (CochainComplex.HomComplex.Cochain.units_smul_v u
      (CochainComplex.HomComplex.δ n m z₀) (-p) (m - p) (by omega)).trans
        ((congrArg (fun f : A.X (-p) ⟶ Q.X (m - p) => u • f) hRaw).trans hWeighted)
  have hd : a ≫ d = P.d p r := by
    change (P.XIsoOfEq (Int.neg_neg p)).inv ≫ P.d (-(-p)) r = P.d p r
    exact inv_XIsoOfEq_d P (Int.neg_neg p) r
  have hv : v = homCochainComponent P Q n z₀ r ≫ e :=
    cochain_v_of_component P Q n z₀ (-p + 1) (m - p) (by omega)
  have hPre : a ≫ (d ≫ v) = pre :=
    (Category.assoc a d v).symm.trans
      ((congrArg (fun f : P.X p ⟶ A.X (-p + 1) => f ≫ v) hd).trans
        ((congrArg (fun f : A.X (-p + 1) ⟶ Q.X (m - p) => P.d p r ≫ f) hv).trans
          (precomp_component_eq P Q n m p z₀ (i := r) (j := p - 1) (by dsimp only [r]; omega)
            (by dsimp only [r]; omega) (by omega))))
  have hPost : a ≫ (u • (v₀ ≫ dQ)) = u • ((a ≫ v₀) ≫ dQ) :=
    (Linear.comp_units_smul a u (v₀ ≫ dQ)).trans
      (congrArg (fun f : P.X p ⟶ Q.X (m - p) => u • f) (Category.assoc a v₀ dQ).symm)
  change a ≫ δz.v (-p) (m - p) (by omega) = pre + u • ((a ≫ v₀) ≫ dQ)
  exact (congrArg (fun f : A.X (-p) ⟶ Q.X (m - p) => a ≫ f) hδ).trans
    ((Preadditive.comp_add (P.X p) (A.X (-p)) (Q.X (m - p)) a
      (u • (v₀ ≫ dQ)) (d ≫ v)).trans
        ((congrArg₂ (fun f g : P.X p ⟶ Q.X (m - p) => f + g) hPost hPre).trans
          (add_comm _ _)))

/-- The product action has the unit dictated by the triangular comparison. -/
def homCyclesBoundaryProductMap (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    AddCommGrpCat.of (∀ i : ℤ, P.cycles i ⟶ Q.homology (n - i)) ⟶
      AddCommGrpCat.of (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶
        Q.homology (n + 1 - p)) := by
  let F : Type v := ∀ i : ℤ, P.cycles i ⟶ Q.homology (n - i)
  let G : Type v := ∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (n + 1 - p)
  let u : ℤˣ := (n + 1).negOnePow
  let b (p : ℤ) : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) :=
    homCyclesBoundaryComponent P p
  let e (p : ℤ) : Q.homology (n - (p - 1)) ⟶ Q.homology (n + 1 - p) :=
    eqToHom (congrArg (fun k : ℤ => (Q.homology k : C))
      (by omega : n - (p - 1) = n + 1 - p))
  let f : F → G := fun z p => u • (b p ≫ z (p - 1) ≫ e p)
  let φ : F →+ G :=
    { toFun := f
      map_zero' := by
        have hp (p : ℤ) : f 0 p = 0 := by
          let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) := b p
          let t : Q.homology (n - (p - 1)) ⟶ Q.homology (n + 1 - p) := e p
          change u • (a ≫ (0 : P.cycles (p - 1) ⟶ Q.homology (n - (p - 1))) ≫ t) = 0
          have hz : a ≫ (0 : P.cycles (p - 1) ⟶ Q.homology (n - (p - 1))) ≫ t = 0 :=
            (Category.assoc a 0 t).symm.trans
              ((congrArg (fun v : (outgoingImageZeroComplex P).X p ⟶
                Q.homology (n - (p - 1)) => v ≫ t) (Limits.comp_zero (f := a))).trans
                  Limits.zero_comp)
          exact (congrArg (fun v : (outgoingImageZeroComplex P).X p ⟶
            Q.homology (n + 1 - p) => u • v) hz).trans (smul_zero u)
        exact funext hp
      map_add' z z' := by
        have hp (p : ℤ) : f (z + z') p = f z p + f z' p := by
          let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) := b p
          let v : P.cycles (p - 1) ⟶ Q.homology (n - (p - 1)) := z (p - 1)
          let v' : P.cycles (p - 1) ⟶ Q.homology (n - (p - 1)) := z' (p - 1)
          let t : Q.homology (n - (p - 1)) ⟶ Q.homology (n + 1 - p) := e p
          have hComp : a ≫ (v + v') ≫ t = a ≫ v ≫ t + a ≫ v' ≫ t := by
            calc
              _ = (a ≫ (v + v')) ≫ t := (Category.assoc a (v + v') t).symm
              _ = (a ≫ v + a ≫ v') ≫ t :=
                congrArg (fun w => w ≫ t)
                  (Preadditive.comp_add ((outgoingImageZeroComplex P).X p) (P.cycles (p - 1))
                    (Q.homology (n - (p - 1))) a v v')
              _ = (a ≫ v) ≫ t + (a ≫ v') ≫ t :=
                Preadditive.add_comp ((outgoingImageZeroComplex P).X p)
                  (Q.homology (n - (p - 1))) (Q.homology (n + 1 - p)) (a ≫ v) (a ≫ v') t
              _ = a ≫ v ≫ t + a ≫ v' ≫ t :=
                congrArg₂ (fun w w' => w + w') (Category.assoc a v t) (Category.assoc a v' t)
          change u • (a ≫ (v + v') ≫ t) = u • (a ≫ v ≫ t) + u • (a ≫ v' ≫ t)
          exact (congrArg (fun w : (outgoingImageZeroComplex P).X p ⟶
            Q.homology (n + 1 - p) => u • w) hComp).trans (smul_add u _ _)
        exact funext hp }
  change AddCommGrpCat.of F ⟶ AddCommGrpCat.of G
  exact AddCommGrpCat.ofHom φ

/-- The connecting map is the δ of the full-product Hom short exact sequence. -/
def homCyclesConnecting (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCochainComplex (cyclesZeroComplex P) Q).homology n ⟶
      (homCochainComplex (outgoingImageZeroComplex P) Q).homology (n + 1) :=
  (homCyclesSequence_shortExact P Q hI).δ n (n + 1) rfl

/-- The connecting map is natural for the same P and Q maps. -/
lemma homCyclesConnecting_naturality {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    homCyclesConnecting P Q n hI ≫
        HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₁ (n + 1) =
      HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₃ n ≫
        homCyclesConnecting P' Q' n hI' :=
  HomologicalComplex.HomologySequence.δ_naturality (homCyclesSequenceMap f g)
    (homCyclesSequence_shortExact P Q hI) (homCyclesSequence_shortExact P' Q' hI')
    n (n + 1) rfl

private lemma homCyclesCycle_post_d (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (z : (homCochainComplex (cyclesZeroComplex P) Q).cycles n) (p : ℤ) :
    homCochainComponent (cyclesZeroComplex P) Q n
        (((homCochainComplex (cyclesZeroComplex P) Q).iCycles n).hom z) p ≫
      Q.d (n - p) (n + 1 - p) = 0 := by
  let S : ChainComplex C ℤ := cyclesZeroComplex P
  let A : CochainComplex C ℤ := (cochainComplexEquivalence C).functor.obj S
  let G : CochainComplex AddCommGrpCat.{v} ℤ := homCochainComplex S Q
  let γ : CochainComplex.HomComplex.Cochain A Q n := (G.iCycles n).hom z
  let i : G.cycles n ⟶ G.X n := G.iCycles n
  let d : G.X n ⟶ G.X (n + 1) := G.d n (n + 1)
  let v : S.X p ⟶ Q.X (n - p) := homCochainComponent S Q n γ p
  let dQ : Q.X (n - p) ⟶ Q.X (n + 1 - p) := Q.d (n - p) (n + 1 - p)
  let u : ℤˣ := (n + 1).negOnePow
  have hz : d.hom γ = 0 :=
    (AddCommGrpCat.comp_apply i d z).symm.trans
      ((ConcreteCategory.congr_hom (G.iCycles_d n (n + 1)) z).trans
        (show (0 : G.cycles n ⟶ G.X (n + 1)).hom z = 0 from rfl))
  have hComponent : homCochainComponent S Q (n + 1) (d.hom γ) p = 0 :=
    (congrArg (fun f : CochainComplex.HomComplex.Cochain A Q (n + 1) =>
      homCochainComponent S Q (n + 1) f p) hz).trans
        (homCochainComponent_zero S Q (n + 1) p)
  have hδ : homCochainComponent S Q (n + 1) (d.hom γ) p = u • (v ≫ dQ) :=
    homCochainComponent_d S Q (by intro i j; rfl) n (n + 1) rfl γ p
  have hZero : u • (v ≫ dQ) = 0 := hδ.symm.trans hComponent
  have hCancel := congrArg (fun f : S.X p ⟶ Q.X (n + 1 - p) => u • f) hZero
  change v ≫ dQ = 0
  simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using hCancel

private lemma XIsoOfEq_hom_d {c : ComplexShape ℤ} (Q : HomologicalComplex C c)
    {i j : ℤ} (h : i = j) (k : ℤ) :
    (Q.XIsoOfEq h).hom ≫ Q.d j k = Q.d i k := by
  subst j
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]

private lemma post_d_zero_of_eq (Q : CochainComplex C ℤ) {i j j' : ℤ} (h : j = j')
    {X : C} (f : X ⟶ Q.X i) (hf : f ≫ Q.d i j = 0) : f ≫ Q.d i j' = 0 := by
  subst j'
  exact hf

private lemma homCyclesBoundaryOperator_cycle (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) :
    (homCochainComplex (cyclesZeroComplex P) Q).iCycles n ≫ homCyclesBoundaryOperator P Q n ≫
        (homCochainComplex (outgoingImageZeroComplex P) Q).d (n + 1) (n + 2) = 0 := by
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A (j : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q j)
  let B (j : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q j)
  let ι : G.cycles n ⟶ A n := G.iCycles n
  let b : A n ⟶ B (n + 1) := homCyclesBoundaryOperator P Q n
  let d : B (n + 1) ⟶ B (n + 2) := F.d (n + 1) (n + 2)
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n := ι.hom z
  let β : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1) :=
    b.hom γ
  have hEval : (ι ≫ b ≫ d).hom z = d.hom β :=
    (AddCommGrpCat.comp_apply ι (b ≫ d) z).trans
      (AddCommGrpCat.comp_apply b d γ)
  change (ι ≫ b ≫ d).hom z = 0
  apply hEval.trans
  apply (homCochainPhysicalPiEquiv (outgoingImageZeroComplex P) Q (n + 2)).injective
  funext p
  let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) :=
    homCyclesBoundaryComponent P p
  let c : P.cycles (p - 1) ⟶ Q.X (n - (p - 1)) :=
    homCochainComponent (cyclesZeroComplex P) Q n γ (p - 1)
  let e : Q.X (n - (p - 1)) ⟶ Q.X (n + 1 - p) :=
    (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom
  let dQ : Q.X (n + 1 - p) ⟶ Q.X (n + 2 - p) := Q.d _ _
  let dQ₀ : Q.X (n - (p - 1)) ⟶ Q.X (n + 2 - p) := Q.d _ _
  have hβ : homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p =
      a ≫ c ≫ e := homCyclesBoundaryOperator_component P Q n p γ
  have he : e ≫ dQ = dQ₀ := XIsoOfEq_hom_d Q (by omega) (n + 2 - p)
  have hc : c ≫ dQ₀ = 0 :=
    post_d_zero_of_eq Q (by omega : n + 1 - (p - 1) = n + 2 - p) c
      (homCyclesCycle_post_d P Q n z (p - 1))
  have hPost :
      homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p ≫ dQ = 0 := by
    calc
      _ = (a ≫ c ≫ e) ≫ dQ := congrArg (fun t => t ≫ dQ) hβ
      _ = a ≫ c ≫ (e ≫ dQ) := by simp only [Category.assoc]
      _ = a ≫ c ≫ dQ₀ := congrArg (fun t => a ≫ c ≫ t) he
      _ = 0 := (congrArg (fun t => a ≫ t) hc).trans (Limits.comp_zero (f := a))
  have hd := homCochainComponent_d (outgoingImageZeroComplex P) Q (by intro i j; rfl)
    (n + 1) (n + 2) (by omega) β p
  change homCochainComponent (outgoingImageZeroComplex P) Q (n + 2) (d.hom β) p =
    homCochainComponent (outgoingImageZeroComplex P) Q (n + 2) 0 p
  exact hd.trans ((congrArg (fun t => (n + 2).negOnePow • t) hPost).trans
    ((smul_zero _).trans (homCochainComponent_zero
      (outgoingImageZeroComplex P) Q (n + 2) p).symm))

/-- The canonical boundary operator maps Hom cycles to Hom cycles. -/
def homCyclesBoundaryCyclesMap (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    (homCochainComplex (cyclesZeroComplex P) Q).cycles n ⟶
      (homCochainComplex (outgoingImageZeroComplex P) Q).cycles (n + 1) :=
  (homCochainComplex (outgoingImageZeroComplex P) Q).liftCycles
    ((homCochainComplex (cyclesZeroComplex P) Q).iCycles n ≫ homCyclesBoundaryOperator P Q n)
    (n + 2) ((ComplexShape.up ℤ).next_eq'
      (ComplexShape.up_mk (n + 1) (n + 2) (by omega)))
    (by exact homCyclesBoundaryOperator_cycle P Q n)

/-- Its cycle inclusion is the full-product boundary operator. -/
@[reassoc]
lemma homCyclesBoundaryCyclesMap_i (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    homCyclesBoundaryCyclesMap P Q n ≫
        (homCochainComplex (outgoingImageZeroComplex P) Q).iCycles (n + 1) =
      (homCochainComplex (cyclesZeroComplex P) Q).iCycles n ≫ homCyclesBoundaryOperator P Q n := by
  unfold homCyclesBoundaryCyclesMap
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

private def homCyclesPoint (P : ChainComplex C ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) (p : ℤ) :
    (cyclesImageSequence P p ((ComplexShape.down ℤ).next p)).Splitting := by
  letI : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := by
    rw [nextDownInt p]
    exact hI p
  exact cyclesImageSequenceSplitting P p ((ComplexShape.down ℤ).next p) rfl

private lemma homCyclesPoint_r_eq (P : ChainComplex C ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) {i j : ℤ} (h : i = j) :
    (P.XIsoOfEq h).inv ≫ (homCyclesPoint P hI i).r =
      (homCyclesPoint P hI j).r ≫ ((cyclesZeroComplex P).XIsoOfEq h).inv := by
  subst j
  let r : P.X i ⟶ (cyclesZeroComplex P).X i := (homCyclesPoint P hI i).r
  change (P.XIsoOfEq (show i = i from rfl)).inv ≫ r =
    r ≫ ((cyclesZeroComplex P).XIsoOfEq (show i = i from rfl)).inv
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv]
  exact (Category.id_comp r).trans (Category.comp_id r).symm

private lemma homCyclesDegreeSplitting_s_component (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (z : (homCochainComplex (cyclesZeroComplex P) Q).X n) (p : ℤ) :
    homCochainComponent P Q n ((homCyclesDegreeSplitting P Q hI n).s.hom z) p =
      (homCyclesPoint P hI p).r ≫ homCochainComponent (cyclesZeroComplex P) Q n z p := by
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let H := homCochainComplex P Q
  let s : G.X n ⟶ H.X n := (homCyclesDegreeSplitting P Q hI n).s
  let z₀ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n := z
  let a : P.X p ⟶ P.X (-(-p)) := (P.XIsoOfEq (Int.neg_neg p)).inv
  let r : P.X (-(-p)) ⟶ (cyclesZeroComplex P).X (-(-p)) :=
    (homCyclesPoint P hI (-(-p))).r
  let r' : P.X p ⟶ (cyclesZeroComplex P).X p := (homCyclesPoint P hI p).r
  let e : (cyclesZeroComplex P).X p ⟶ (cyclesZeroComplex P).X (-(-p)) :=
    ((cyclesZeroComplex P).XIsoOfEq (Int.neg_neg p)).inv
  let v : (cyclesZeroComplex P).X (-(-p)) ⟶ Q.X (n - p) :=
    z₀.v (-p) (n - p) (by omega)
  have hs : ((s.hom z₀).v (-p) (n - p) (by omega)) = r ≫ v := rfl
  have hr : a ≫ r = r' ≫ e := homCyclesPoint_r_eq P hI (Int.neg_neg p)
  change a ≫ ((s.hom z₀).v (-p) (n - p) (by omega)) = r' ≫ (e ≫ v)
  exact (congrArg (fun t => a ≫ t) hs).trans
    ((Category.assoc a r v).symm.trans
      ((congrArg (fun t => t ≫ v) hr).trans (Category.assoc r' e v)))

private lemma homCyclesPoint_toCycles (P : ChainComplex C ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) (p : ℤ) :
    P.d p (p - 1) ≫ (homCyclesPoint P hI (p - 1)).r = P.toCycles p (p - 1) := by
  let t : P.X p ⟶ P.cycles (p - 1) := P.toCycles p (p - 1)
  let i : P.cycles (p - 1) ⟶ P.X (p - 1) := P.iCycles (p - 1)
  let r : P.X (p - 1) ⟶ P.cycles (p - 1) := (homCyclesPoint P hI (p - 1)).r
  have hti : t ≫ i = P.d p (p - 1) := P.toCycles_i p (p - 1)
  have hir : i ≫ r = 𝟙 (P.cycles (p - 1)) := by
    have h := (homCyclesPoint P hI (p - 1)).f_r
    change i ≫ r = 𝟙 (P.cycles (p - 1)) at h
    exact h
  change P.d p (p - 1) ≫ r = t
  exact (congrArg (fun a => a ≫ r) hti.symm).trans
    ((Category.assoc t i r).trans
      ((congrArg (fun a => t ≫ a) hir).trans (Category.comp_id t)))

private lemma homCyclesConnecting_lift (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ((homCochainComplex (cyclesZeroComplex P) Q).iCycles n ≫
        homCyclesBoundaryOperator P Q n) ≫ (homCyclesSequence P Q).f.f (n + 1) =
      ((homCochainComplex (cyclesZeroComplex P) Q).iCycles n ≫
        (homCyclesDegreeSplitting P Q hI n).s) ≫ (homCochainComplex P Q).d n (n + 1) := by
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let H := homCochainComplex P Q
  let A (j : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q j)
  let B (j : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q j)
  let D (j : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q j)
  let ι : G.cycles n ⟶ A n := G.iCycles n
  let b : A n ⟶ B (n + 1) := homCyclesBoundaryOperator P Q n
  let τ : B (n + 1) ⟶ D (n + 1) := (homCyclesSequence P Q).f.f (n + 1)
  let s : A n ⟶ D n := (homCyclesDegreeSplitting P Q hI n).s
  let d : D n ⟶ D (n + 1) := H.d n (n + 1)
  let qP : P ⟶ outgoingImageZeroComplex P :=
    (cyclesComplexProjection (C := C) (c := ComplexShape.down ℤ)).app P
  have hτ : τ = (homCochainComplexMap qP (𝟙 Q)).f (n + 1) := rfl
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n := ι.hom z
  let β : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1) :=
    b.hom γ
  let α : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n := s.hom γ
  have hLeft : ((ι ≫ b) ≫ τ).hom z = τ.hom β :=
    (AddCommGrpCat.comp_apply (ι ≫ b) τ z).trans
      (congrArg τ.hom (AddCommGrpCat.comp_apply ι b z))
  have hRight : ((ι ≫ s) ≫ d).hom z = d.hom α :=
    (AddCommGrpCat.comp_apply (ι ≫ s) d z).trans
      (congrArg d.hom (AddCommGrpCat.comp_apply ι s z))
  have hValue : τ.hom β = d.hom α := by
    apply (homCochainPhysicalPiEquiv P Q (n + 1)).injective
    funext p
    let κ : P.X p ⟶ (outgoingImageZeroComplex P).X p := qP.f p
    let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) :=
      homCyclesBoundaryComponent P p
    let c : P.cycles (p - 1) ⟶ Q.X (n - (p - 1)) :=
      homCochainComponent (cyclesZeroComplex P) Q n γ (p - 1)
    let c₀ : P.cycles p ⟶ Q.X (n - p) :=
      homCochainComponent (cyclesZeroComplex P) Q n γ p
    let e : Q.X (n - (p - 1)) ⟶ Q.X (n + 1 - p) :=
      (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom
    let dP : P.X p ⟶ P.X (p - 1) := P.d p (p - 1)
    let dQ : Q.X (n - p) ⟶ Q.X (n + 1 - p) := Q.d _ _
    let r : P.X (p - 1) ⟶ P.cycles (p - 1) := (homCyclesPoint P hI (p - 1)).r
    let r₀ : P.X p ⟶ P.cycles p := (homCyclesPoint P hI p).r
    let t : P.X p ⟶ P.cycles (p - 1) := P.toCycles p (p - 1)
    have hτValue : τ.hom β = ((homCochainComplexMap qP (𝟙 Q)).f (n + 1)).hom β :=
      congrArg (fun f : B (n + 1) ⟶ D (n + 1) => f.hom β) hτ
    have hMap := homCochainComponent_map qP (𝟙 Q) (n + 1) p β
    have hId : (𝟙 Q : Q ⟶ Q).f (n + 1 - p) = 𝟙 (Q.X (n + 1 - p)) := rfl
    have hMapValue : homCochainComponent P Q (n + 1) (τ.hom β) p =
        κ ≫ homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p :=
      (congrArg (fun z : CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence C).functor.obj P) Q (n + 1) =>
            homCochainComponent P Q (n + 1) z p) hτValue).trans
        (hMap.trans ((congrArg (fun v : Q.X (n + 1 - p) ⟶ Q.X (n + 1 - p) =>
          κ ≫ homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p ≫ v)
            hId).trans
          (congrArg (fun v => κ ≫ v)
            (Category.comp_id (homCochainComponent
              (outgoingImageZeroComplex P) Q (n + 1) β p)))))
    have hβ : homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p =
        a ≫ c ≫ e := homCyclesBoundaryOperator_component P Q n p γ
    have hκ : κ = Abelian.factorThruImage (P.d p ((ComplexShape.down ℤ).next p)) := rfl
    have hκa : κ ≫ a = t :=
      (congrArg (fun v => v ≫ a) hκ).trans (quotient_homCyclesBoundaryComponent P p)
    have hL : homCochainComponent P Q (n + 1) (τ.hom β) p = t ≫ c ≫ e :=
      hMapValue.trans ((congrArg (fun v => κ ≫ v) hβ).trans
        ((Category.assoc κ a (c ≫ e)).symm.trans
          (congrArg (fun v => v ≫ c ≫ e) hκa)))
    have h₁ : homCochainComponent P Q n α (p - 1) = r ≫ c :=
      homCyclesDegreeSplitting_s_component P Q n hI γ (p - 1)
    have h₀ : homCochainComponent P Q n α p = r₀ ≫ c₀ :=
      homCyclesDegreeSplitting_s_component P Q n hI γ p
    have hδ : homCochainComponent P Q (n + 1) (d.hom α) p =
        dP ≫ homCochainComponent P Q n α (p - 1) ≫ e +
          (n + 1).negOnePow • (homCochainComponent P Q n α p ≫ dQ) :=
      homCochainComponent_d_general P Q n (n + 1) rfl α p
    have hExpanded : homCochainComponent P Q (n + 1) (d.hom α) p =
        dP ≫ (r ≫ c) ≫ e + (n + 1).negOnePow • ((r₀ ≫ c₀) ≫ dQ) :=
      hδ.trans (congrArg₂ (fun x y : P.X p ⟶ Q.X (n + 1 - p) => x + y)
        (congrArg (fun v => dP ≫ v ≫ e) h₁)
        (congrArg (fun v => (n + 1).negOnePow • (v ≫ dQ)) h₀))
    have hz : c₀ ≫ dQ = 0 := homCyclesCycle_post_d P Q n z p
    have hPost : (r₀ ≫ c₀) ≫ dQ = 0 :=
      (Category.assoc r₀ c₀ dQ).trans
        ((congrArg (fun v => r₀ ≫ v) hz).trans (Limits.comp_zero (f := r₀)))
    have hPre : dP ≫ (r ≫ c) ≫ e = t ≫ c ≫ e :=
      (congrArg (fun v => dP ≫ v) (Category.assoc r c e)).trans
        ((Category.assoc dP r (c ≫ e)).symm.trans
          (congrArg (fun v => v ≫ c ≫ e) (homCyclesPoint_toCycles P hI p)))
    have hR : homCochainComponent P Q (n + 1) (d.hom α) p = t ≫ c ≫ e :=
      hExpanded.trans
        ((congrArg₂ (fun x y : P.X p ⟶ Q.X (n + 1 - p) => x + y) hPre
          ((congrArg (fun v => (n + 1).negOnePow • v) hPost).trans
            (smul_zero (n + 1).negOnePow))).trans (add_zero _))
    change homCochainComponent P Q (n + 1) (τ.hom β) p =
      homCochainComponent P Q (n + 1) (d.hom α) p
    exact hL.trans hR.symm
  change ((ι ≫ b) ≫ τ).hom z = ((ι ≫ s) ≫ d).hom z
  exact hLeft.trans (hValue.trans hRight.symm)

/-- The connecting map has the boundary-cycle representative. -/
@[reassoc]
lemma homCyclesConnecting_homologyπ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCochainComplex (cyclesZeroComplex P) Q).homologyπ n ≫ homCyclesConnecting P Q n hI =
      homCyclesBoundaryCyclesMap P Q n ≫
        (homCochainComplex (outgoingImageZeroComplex P) Q).homologyπ (n + 1) := by
  let S := homCyclesSequence P Q
  let G : CochainComplex AddCommGrpCat.{v} ℤ := S.X₃
  let F : CochainComplex AddCommGrpCat.{v} ℤ := S.X₁
  let H : CochainComplex AddCommGrpCat.{v} ℤ := S.X₂
  let t := homCyclesDegreeSplitting P Q hI n
  let ι : G.cycles n ⟶ G.X n := G.iCycles n
  let s : G.X n ⟶ H.X n := t.s
  let g : H.X n ⟶ G.X n := S.g.f n
  let b : G.X n ⟶ F.X (n + 1) := homCyclesBoundaryOperator P Q n
  let x₂ : G.cycles n ⟶ H.X n := ι ≫ s
  let x₁ : G.cycles n ⟶ F.X (n + 1) := ι ≫ b
  let πG : G.cycles n ⟶ G.homology n := G.homologyπ n
  let πF : F.cycles (n + 1) ⟶ F.homology (n + 1) := F.homologyπ (n + 1)
  let δ : G.homology n ⟶ F.homology (n + 1) := homCyclesConnecting P Q n hI
  let k : G.cycles n ⟶ F.cycles (n + 1) := homCyclesBoundaryCyclesMap P Q n
  let hS : S.ShortExact := homCyclesSequence_shortExact P Q hI
  have hs : s ≫ g = 𝟙 (G.X n) := by
    have h := t.s_g
    change s ≫ g = 𝟙 (G.X n) at h
    exact h
  have hx₂ : x₂ ≫ g = ι :=
    (Category.assoc ι s g).trans
      ((congrArg (fun v => ι ≫ v) hs).trans (Category.comp_id ι))
  have hx₃ : ι ≫ G.d n (n + 1) = 0 := G.iCycles_d n (n + 1)
  have hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ H.d n (n + 1) :=
    homCyclesConnecting_lift P Q n hI
  have hNext₀ : (ComplexShape.up ℤ).next n = n + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl)
  have hNext₁ : (ComplexShape.up ℤ).next (n + 1) = n + 2 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk (n + 1) (n + 2) (by omega))
  let l₀ : G.cycles n ⟶ G.cycles n := G.liftCycles ι (n + 1) hNext₀ hx₃
  let l₁ : G.cycles n ⟶ F.cycles (n + 1) :=
    F.liftCycles x₁ (n + 2) hNext₁ (by exact homCyclesBoundaryOperator_cycle P Q n)
  have h : l₀ ≫ πG ≫ δ = l₁ ≫ πF :=
    hS.δ_eq n (n + 1) rfl ι hx₃ x₂ hx₂ x₁ hx₁ (n + 2) hNext₁
  have hl₀ : l₀ = 𝟙 (G.cycles n) := by
    apply (cancel_mono ι).1
    exact (G.liftCycles_i ι (n + 1) hNext₀ hx₃).trans (Category.id_comp ι).symm
  have hl₁ : l₁ = k := rfl
  have hLeft : l₀ ≫ πG ≫ δ = πG ≫ δ :=
    (congrArg (fun v => v ≫ πG ≫ δ) hl₀).trans (Category.id_comp (πG ≫ δ))
  have hRight : l₁ ≫ πF = k ≫ πF := congrArg (fun v => v ≫ πF) hl₁
  change πG ≫ δ = k ≫ πF
  exact hLeft.symm.trans (h.trans hRight)

/-- The lifted boundary retains the Q-cycle component and its target-degree equality. -/
lemma homCyclesBoundaryCyclesMap_component (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p : ℤ) (z : (homCochainComplex (cyclesZeroComplex P) Q).cycles n) :
    homZeroSourceCycleComponent (outgoingImageZeroComplex P) Q (n + 1)
        (by intro i j; rfl) (homCyclesBoundaryCyclesMap P Q n z) p =
      homCyclesBoundaryComponent P p ≫
        homZeroSourceCycleComponent (cyclesZeroComplex P) Q n (by intro i j; rfl)
          z (p - 1) ≫ eqToHom (congrArg (fun r : ℤ => (Q.cycles r : C))
            (by omega : n - (p - 1) = n + 1 - p)) := by
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n)
  let D : AddCommGrpCat.{v} := AddCommGrpCat.of
    (CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1))
  let k : G.cycles n ⟶ F.cycles (n + 1) := homCyclesBoundaryCyclesMap P Q n
  let ιG : G.cycles n ⟶ A := G.iCycles n
  let ιF : F.cycles (n + 1) ⟶ D := F.iCycles (n + 1)
  let b : A ⟶ D := homCyclesBoundaryOperator P Q n
  let γ : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n := ιG.hom z
  let β : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1) :=
    ιF.hom (k.hom z)
  have hPack : k ≫ ιF = ιG ≫ b := homCyclesBoundaryCyclesMap_i P Q n
  have hValue : β = b.hom γ :=
    (AddCommGrpCat.comp_apply k ιF z).symm.trans
      ((ConcreteCategory.congr_hom hPack z).trans (AddCommGrpCat.comp_apply ιG b z))
  let x : (outgoingImageZeroComplex P).X p ⟶ Q.cycles (n + 1 - p) :=
    homZeroSourceCycleComponent (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl) (k.hom z) p
  let y : P.cycles (p - 1) ⟶ Q.cycles (n - (p - 1)) :=
    homZeroSourceCycleComponent (cyclesZeroComplex P) Q n (by intro i j; rfl) z (p - 1)
  let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) :=
    homCyclesBoundaryComponent P p
  let i₀ : Q.cycles (n - (p - 1)) ⟶ Q.X (n - (p - 1)) := Q.iCycles _
  let i₁ : Q.cycles (n + 1 - p) ⟶ Q.X (n + 1 - p) := Q.iCycles _
  let e : Q.X (n - (p - 1)) ⟶ Q.X (n + 1 - p) :=
    (Q.XIsoOfEq (by omega : n - (p - 1) = n + 1 - p)).hom
  let ec : Q.cycles (n - (p - 1)) ⟶ Q.cycles (n + 1 - p) :=
    eqToHom (congrArg (fun r : ℤ => (Q.cycles r : C))
      (by omega : n - (p - 1) = n + 1 - p))
  have hx : x ≫ i₁ = homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p :=
    homZeroSourceCycleComponent_i (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl) (k.hom z) p
  have hy : y ≫ i₀ = homCochainComponent (cyclesZeroComplex P) Q n γ (p - 1) :=
    homZeroSourceCycleComponent_i (cyclesZeroComplex P) Q n (by intro i j; rfl) z (p - 1)
  have hβ : homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) β p =
      a ≫ homCochainComponent (cyclesZeroComplex P) Q n γ (p - 1) ≫ e :=
    (congrArg (fun w : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q (n + 1) =>
          homCochainComponent (outgoingImageZeroComplex P) Q (n + 1) w p) hValue).trans
      (homCyclesBoundaryOperator_component P Q n p γ)
  have he : ec ≫ i₁ = i₀ ≫ e := cyclesEq_iCycles Q (by omega)
  have hRight : (a ≫ y ≫ ec) ≫ i₁ = a ≫ (y ≫ i₀) ≫ e := by
    calc
      _ = a ≫ y ≫ (ec ≫ i₁) := by simp only [Category.assoc]
      _ = a ≫ y ≫ (i₀ ≫ e) := congrArg (fun v => a ≫ y ≫ v) he
      _ = a ≫ (y ≫ i₀) ≫ e := by simp only [Category.assoc]
  apply (cancel_mono i₁).1
  change x ≫ i₁ = (a ≫ y ≫ ec) ≫ i₁
  exact hx.trans (hβ.trans
    ((congrArg (fun v => a ≫ v ≫ e) hy.symm).trans hRight.symm))

/-- The δ has the product characteristic before source-term projectivity. -/
lemma homCyclesConnecting_productSquare (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    homCyclesConnecting P Q n hI ≫
        homZeroSourceCohomologyComparison (outgoingImageZeroComplex P) Q (n + 1)
          (by intro i j; rfl) =
      homZeroSourceCohomologyComparison (cyclesZeroComplex P) Q n (by intro i j; rfl) ≫
        homCyclesBoundaryProductMap P Q n := by
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let PG : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let PF : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (n + 1 - p))
  let πG : G.cycles n ⟶ G.homology n := G.homologyπ n
  let πF : F.cycles (n + 1) ⟶ F.homology (n + 1) := F.homologyπ (n + 1)
  let δ : G.homology n ⟶ F.homology (n + 1) := homCyclesConnecting P Q n hI
  let qG : G.homology n ⟶ PG :=
    homZeroSourceCohomologyComparison (cyclesZeroComplex P) Q n (by intro i j; rfl)
  let qF : F.homology (n + 1) ⟶ PF :=
    homZeroSourceCohomologyComparison (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl)
  let cG : G.cycles n ⟶ PG :=
    homZeroSourceCycleMap (cyclesZeroComplex P) Q n (by intro i j; rfl)
  let cF : F.cycles (n + 1) ⟶ PF :=
    homZeroSourceCycleMap (outgoingImageZeroComplex P) Q (n + 1) (by intro i j; rfl)
  let b : G.cycles n ⟶ F.cycles (n + 1) := homCyclesBoundaryCyclesMap P Q n
  let m : PG ⟶ PF := homCyclesBoundaryProductMap P Q n
  have hδ : πG ≫ δ = b ≫ πF := homCyclesConnecting_homologyπ P Q n hI
  have hG : πG ≫ qG = cG :=
    homologyπ_homZeroSourceCohomologyComparison (cyclesZeroComplex P) Q n
      (by intro i j; rfl)
  have hF : πF ≫ qF = cF :=
    homologyπ_homZeroSourceCohomologyComparison (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl)
  have hCycle : b ≫ cF = cG ≫ m := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    have hLeft : (b ≫ cF).hom z = cF.hom (b.hom z) := AddCommGrpCat.comp_apply b cF z
    have hRight : (cG ≫ m).hom z = m.hom (cG.hom z) := AddCommGrpCat.comp_apply cG m z
    have hValue : cF.hom (b.hom z) = m.hom (cG.hom z) := by
      funext p
      let a : (outgoingImageZeroComplex P).X p ⟶ P.cycles (p - 1) :=
        homCyclesBoundaryComponent P p
      let x : (outgoingImageZeroComplex P).X p ⟶ Q.cycles (n + 1 - p) :=
        homZeroSourceCycleComponent (outgoingImageZeroComplex P) Q (n + 1)
          (by intro i j; rfl) (b.hom z) p
      let y : P.cycles (p - 1) ⟶ Q.cycles (n - (p - 1)) :=
        homZeroSourceCycleComponent (cyclesZeroComplex P) Q n (by intro i j; rfl) z (p - 1)
      let π₀ : Q.cycles (n - (p - 1)) ⟶ Q.homology (n - (p - 1)) := Q.homologyπ _
      let π₁ : Q.cycles (n + 1 - p) ⟶ Q.homology (n + 1 - p) := Q.homologyπ _
      let ec : Q.cycles (n - (p - 1)) ⟶ Q.cycles (n + 1 - p) :=
        eqToHom (congrArg (fun r : ℤ => (Q.cycles r : C))
          (by omega : n - (p - 1) = n + 1 - p))
      let eh : Q.homology (n - (p - 1)) ⟶ Q.homology (n + 1 - p) :=
        eqToHom (congrArg (fun r : ℤ => (Q.homology r : C))
          (by omega : n - (p - 1) = n + 1 - p))
      have hx : x = a ≫ y ≫ ec := homCyclesBoundaryCyclesMap_component P Q n p z
      have hπ : π₀ ≫ eh = ec ≫ π₁ := homologyπ_eq Q (by omega)
      have hPost : (a ≫ y ≫ ec) ≫ π₁ = a ≫ (y ≫ π₀) ≫ eh := by
        calc
          _ = a ≫ y ≫ (ec ≫ π₁) := by simp only [Category.assoc]
          _ = a ≫ y ≫ (π₀ ≫ eh) := congrArg (fun v => a ≫ y ≫ v) hπ.symm
          _ = a ≫ (y ≫ π₀) ≫ eh := by simp only [Category.assoc]
      have hL : cF.hom (b.hom z) p = Int.triangularSign (n + 1) • (x ≫ π₁) := rfl
      have hR : m.hom (cG.hom z) p =
          (n + 1).negOnePow • (a ≫ (Int.triangularSign n • (y ≫ π₀)) ≫ eh) := rfl
      have hScalar :
          (n + 1).negOnePow • (a ≫ (Int.triangularSign n • (y ≫ π₀)) ≫ eh) =
            ((n + 1).negOnePow * Int.triangularSign n) • (a ≫ (y ≫ π₀) ≫ eh) := by
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
      have hSign : Int.triangularSign (n + 1) =
          (n + 1).negOnePow * Int.triangularSign n :=
        (Int.triangularSign_succ n).trans
          (mul_comm (Int.triangularSign n) ((n + 1).negOnePow))
      exact hL.trans ((congrArg (fun v => Int.triangularSign (n + 1) • (v ≫ π₁)) hx).trans
        ((congrArg (fun v => Int.triangularSign (n + 1) • v) hPost).trans
          ((congrArg (fun u : ℤˣ => u • (a ≫ (y ≫ π₀) ≫ eh)) hSign).trans
            (hScalar.symm.trans hR.symm))))
    exact hLeft.trans (hValue.trans hRight.symm)
  have hLeft : πG ≫ (δ ≫ qF) = b ≫ cF :=
    (Category.assoc πG δ qF).symm.trans
      ((congrArg (fun v => v ≫ qF) hδ).trans
        ((Category.assoc b πF qF).trans (congrArg (fun v => b ≫ v) hF)))
  have hRight : πG ≫ (qG ≫ m) = cG ≫ m :=
    (Category.assoc πG qG m).symm.trans (congrArg (fun v => v ≫ m) hG)
  apply (cancel_epi πG).1
  change πG ≫ (δ ≫ qF) = πG ≫ (qG ≫ m)
  exact hLeft.trans (hCycle.trans hRight.symm)

/-- Projective cycles identify the same connecting map with its full product map. -/
lemma homCyclesConnecting_isoFormula (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p, Projective ((cyclesZeroComplex P).X p)) :
    let hOut : ∀ p, Projective ((outgoingImageZeroComplex P).X p) := fun p => by
      change Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))
      rw [nextDownInt p]
      exact hI p
    (homZeroSourceCohomologyIso (cyclesZeroComplex P) Q n (by intro i j; rfl) hZ).inv ≫
        homCyclesConnecting P Q n hI ≫
        (homZeroSourceCohomologyIso (outgoingImageZeroComplex P) Q (n + 1)
          (by intro i j; rfl) hOut).hom = homCyclesBoundaryProductMap P Q n := by
  let hOut : ∀ p, Projective ((outgoingImageZeroComplex P).X p) := fun p => by
    change Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))
    rw [nextDownInt p]
    exact hI p
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let PG : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let PF : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (n + 1 - p))
  let e : G.homology n ≅ PG :=
    homZeroSourceCohomologyIso (cyclesZeroComplex P) Q n (by intro i j; rfl) hZ
  let e' : F.homology (n + 1) ≅ PF :=
    homZeroSourceCohomologyIso (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl) hOut
  let qG : G.homology n ⟶ PG :=
    homZeroSourceCohomologyComparison (cyclesZeroComplex P) Q n (by intro i j; rfl)
  let qF : F.homology (n + 1) ⟶ PF :=
    homZeroSourceCohomologyComparison (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl)
  let δ : G.homology n ⟶ F.homology (n + 1) := homCyclesConnecting P Q n hI
  let m : PG ⟶ PF := homCyclesBoundaryProductMap P Q n
  have he : e.hom = qG :=
    homZeroSourceCohomologyIso_hom (cyclesZeroComplex P) Q n (by intro i j; rfl) hZ
  have he' : e'.hom = qF :=
    homZeroSourceCohomologyIso_hom (outgoingImageZeroComplex P) Q (n + 1)
      (by intro i j; rfl) hOut
  have hSquare : δ ≫ qF = qG ≫ m := homCyclesConnecting_productSquare P Q n hI
  have hNative : δ ≫ e'.hom = e.hom ≫ m :=
    (congrArg (fun v => δ ≫ v) he').trans
      (hSquare.trans (congrArg (fun v => v ≫ m) he.symm))
  change e.inv ≫ δ ≫ e'.hom = m
  exact (congrArg (fun v => e.inv ≫ v) hNative).trans
    ((Category.assoc e.inv e.hom m).symm.trans
      ((congrArg (fun v => v ≫ m) e.inv_hom_id).trans (Category.id_comp m)))

end ChainComplex
