/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.HomFixedCoefficient
public import MathlibExt.Algebra.Homology.ShortComplex.MorphismExt

/-!
# Naturality of the fixed-coefficient universal coefficient sequence

Let C be abelian, f : P′ → P an integer chain map and b : M → M′. Assume all terms and
differential images of P and P′ are projective. The fixed-coefficient UCT short exact sequences
0 → Ext¹_C(Hₙ₋₁(P),M) → Hⁿ Hom(P,M) → Hom_C(Hₙ(P),M) → 0 then form a commutative diagram with
the corresponding sequence for (P′,M′).

The left vertical map is Ext pullback along Hₙ₋₁(f) followed by pushforward along b. The middle
map is Hⁿ Hom(f,b), and the right map sends t to b ∘ t ∘ Hₙ(f). The Ext injections use positive
Yoneda normalization. The diagram is independent of any chosen UCT splitting, and satisfies the
identity and composition laws in both variables.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.Abelian HomologicalComplex

namespace ChainComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {P P' : ChainComplex C ℤ} {M M' : C}

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The induced map of short exact sequences is Ext pullback/pushforward
on the left, Hⁿ Hom(f,b) in the middle, and t ↦ b ∘ t ∘ Hₙ(f) on the right; no chosen splitting
enters it. -/
def homFixedCoefficientUniversalCoefficientSequenceMap
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI ⟶
      homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P' M' n hP' hI' := by
  let g := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let c := homFixedCoefficientUCTCoordinates P M n
  let c' := homFixedCoefficientUCTCoordinates P' M' n
  exact ShortComplex.changeObjectsMap
    (homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI')
    c.1 c.2.1 c.2.2 c'.1 c'.2.1 c'.2.2

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The concentrated-target isomorphisms from the full-product UCT for
(P,M[0]) to the fixed-coefficient UCT commute with the full Hom/Ext sequence map induced by
(f,b[0]) and the fixed-coefficient sequence map induced by (f,b). -/
@[reassoc]
lemma homFixedCoefficientUniversalCoefficientSequenceIso_hom_naturality
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    homUniversalCoefficientSequenceEngineMap f
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b)
        n hP hI hP' hI' ≫
        (homFixedCoefficientUniversalCoefficientSequenceIso P' M' n hP' hI').hom =
      (homFixedCoefficientUniversalCoefficientSequenceIso P M n hP hI).hom ≫
        homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI' := by
  let g := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let c := homFixedCoefficientUCTCoordinates P M n
  let c' := homFixedCoefficientUCTCoordinates P' M' n
  exact ShortComplex.changeObjectsIso_hom_naturality
    (homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI')
    c.1 c.2.1 c.2.2 c'.1 c'.2.1 c'.2.2

private lemma homFixedCoefficientUCTCoordinates_left_naturality
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ) :
    (homUctProductPresentationMap f
        (fun p => HomologicalComplex.homologyMap
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b) (n - 1 - p))).τ₃ ≫
        (homFixedCoefficientUCTCoordinates P' M' n).1.hom =
      (homFixedCoefficientUCTCoordinates P M n).1.hom ≫
        AddCommGrpCat.uliftFunctor.{v, w}.map
          (((extFunctor 1).map (HomologicalComplex.homologyMap f (n - 1)).op).app M ≫
            (extFunctorObj (P'.homology (n - 1)) 1).map b) := by
  let Q : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Q' : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M'
  let g : Q ⟶ Q' := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let A : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{v, w} (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1))
  let A' : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{v, w} (Ext.{w} (P'.homology p) (Q'.homology (n - 1 - p)) 1))
  let E : AddCommGrpCat.{w} := AddCommGrpCat.of (Ext.{w} (P.homology (n - 1)) M 1)
  let E' : AddCommGrpCat.{w} := AddCommGrpCat.of (Ext.{w} (P'.homology (n - 1)) M' 1)
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let t : E ⟶ E' :=
    ((extFunctor 1).map (HomologicalComplex.homologyMap f (n - 1)).op).app M ≫
      (extFunctorObj (P'.homology (n - 1)) 1).map b
  let m₀ := (homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - 1 - p))).τ₃
  change A ⟶ A' at m₀
  let m : A ⟶ A' := m₀
  let c : A ≅ V.obj E := (homFixedCoefficientUCTCoordinates P M n).1
  let c' : A' ≅ V.obj E' := (homFixedCoefficientUCTCoordinates P' M' n).1
  let θ : ℤˣ := (Int.triangularSign n)⁻¹
  have ht (x : E) : t.hom x =
      ((show Ext.{w} (P'.homology (n - 1)) (P.homology (n - 1)) 0 from
        Ext.mk₀ (HomologicalComplex.homologyMap f (n - 1))).comp x
          (zero_add 1)).comp (show Ext.{w} M M' 0 from Ext.mk₀ b) (add_zero 1) := rfl
  apply AddCommGrpCat.ext
  intro x
  let z : ∀ p : ℤ, Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1 :=
    fun p => (x p).down
  let z' : ∀ p : ℤ, Ext.{w} (P'.homology p) (Q'.homology (n - 1 - p)) 1 := fun p =>
    ((show Ext.{w} (P'.homology p) (P.homology p) 0 from
      Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (z p) (zero_add 1)).comp
        (show Ext.{w} (Q.homology (n - 1 - p)) (Q'.homology (n - 1 - p)) 0 from
          Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)
  have hm (p : ℤ) : m.hom x p = ULift.up (z' p) :=
    homUctProductPresentationMap_τ₃_apply f
      (fun p => HomologicalComplex.homologyMap g (n - 1 - p)) x p
  have hFamily : (fun p : ℤ => (m.hom x p).down) = z' := by
    funext p
    exact congrArg
      (fun y : ULift.{v, w} (Ext.{w} (P'.homology p) (Q'.homology (n - 1 - p)) 1) =>
        y.down) (hm p)
  let y : E := homFixedCoefficientExtProductEquiv P M n z
  have hCollapse : homFixedCoefficientExtProductEquiv P' M' n z' = t.hom y :=
    (homFixedCoefficientExtProductEquiv_naturality f b n z).trans (ht y).symm
  have hSource : c.hom.hom x = ULift.up (θ • y) :=
    homFixedCoefficientUCTCoordinates_left_apply P M n x
  have hTarget : c'.hom.hom (m.hom x) =
      ULift.up (θ • homFixedCoefficientExtProductEquiv P' M' n
        (fun p : ℤ => (m.hom x p).down)) :=
    homFixedCoefficientUCTCoordinates_left_apply P' M' n (m.hom x)
  have hLeft : (m ≫ c'.hom).hom x = ULift.up (θ • t.hom y) :=
    (AddCommGrpCat.comp_apply m c'.hom x).trans
      (hTarget.trans
        ((congrArg (fun z => ULift.up (θ • homFixedCoefficientExtProductEquiv P' M' n z))
          hFamily).trans
            (congrArg (fun z : E' => ULift.up (θ • z)) hCollapse)))
  have htUnit : t.hom (θ • y) = θ • t.hom y := by
    change t.hom ((θ : ℤ) • y) = (θ : ℤ) • t.hom y
    exact t.hom.map_zsmul (θ : ℤ) y
  have hRight : (c.hom ≫ V.map t).hom x = ULift.up (θ • t.hom y) :=
    (AddCommGrpCat.comp_apply c.hom (V.map t) x).trans
      ((congrArg (V.map t).hom hSource).trans
        ((show (V.map t).hom (ULift.up (θ • y)) = ULift.up (t.hom (θ • y)) from rfl).trans
          (congrArg ULift.up htUnit)))
  change (m ≫ c'.hom).hom x = (c.hom ≫ V.map t).hom x
  exact hLeft.trans hRight.symm

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The left vertical map Ext¹_C(Hₙ₋₁(P),M) → Ext¹_C(Hₙ₋₁(P′),M′) is
pullback along Hₙ₋₁(f) followed by pushforward along b. The endpoint degree units cancel, so no
extra sign occurs. -/
lemma homFixedCoefficientUniversalCoefficientSequenceMap_τ₁
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI').τ₁ =
      AddCommGrpCat.uliftFunctor.{v, w}.map
        (((extFunctor 1).map (HomologicalComplex.homologyMap f (n - 1)).op).app M ≫
          (extFunctorObj (P'.homology (n - 1)) 1).map b) := by
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let g := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let m := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let c := (homFixedCoefficientUCTCoordinates P M n).1
  let c' := (homFixedCoefficientUCTCoordinates P' M' n).1
  let t := ((extFunctor 1).map (HomologicalComplex.homologyMap f (n - 1)).op).app M ≫
    (extFunctorObj (P'.homology (n - 1)) 1).map b
  have hm : m.τ₁ = (homUctProductPresentationMap f
      (fun p => HomologicalComplex.homologyMap g (n - 1 - p))).τ₃ := rfl
  have hC : m.τ₁ ≫ c'.hom = c.hom ≫ V.map t :=
    (congrArg (fun a => a ≫ c'.hom) hm).trans
      (homFixedCoefficientUCTCoordinates_left_naturality f b n)
  change c.inv ≫ (m.τ₁ ≫ c'.hom) = V.map t
  exact (congrArg (fun a => c.inv ≫ a) hC).trans (c.inv_hom_id_assoc (V.map t))

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The middle vertical map is precisely the common-universe lift of Hⁿ
Hom(f,b), where Hom(f,b) has components k ↦ b ∘ k ∘ fₚ. -/
lemma homFixedCoefficientUniversalCoefficientSequenceMap_τ₂
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI').τ₂ =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homFixedCoefficientMap f b) n) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n
  let Q := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M
  let Q' := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M'
  let g : Q ⟶ Q' := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map b
  let a := homCochainComplexMap f g
  let e := homFixedCoefficientIso P M
  let e' := homFixedCoefficientIso P' M'
  let t := (homFixedCoefficientUCTCoordinates P M n).2.1
  let t' := (homFixedCoefficientUCTCoordinates P' M' n).2.1
  let m := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let r := U.map (H.map (homFixedCoefficientMap f b))
  have hH : H.map a ≫ H.map e'.hom = H.map e.hom ≫
      H.map (homFixedCoefficientMap f b) :=
    (H.map_comp a e'.hom).symm.trans
      ((congrArg H.map (homFixedCoefficientIso_naturality f b)).trans
        (H.map_comp e.hom (homFixedCoefficientMap f b)))
  have hU : U.map (H.map a) ≫ t'.hom = t.hom ≫ r :=
    (U.map_comp (H.map a) (H.map e'.hom)).symm.trans
      ((congrArg U.map hH).trans
        (U.map_comp (H.map e.hom) (H.map (homFixedCoefficientMap f b))))
  have hm : m.τ₂ = U.map (H.map a) :=
    homUniversalCoefficientSequenceEngineMap_τ₂ f g n hP hI hP' hI'
  change t.inv ≫ (m.τ₂ ≫ t'.hom) = r
  exact (congrArg (fun z => t.inv ≫ (z ≫ t'.hom)) hm).trans
    ((congrArg (fun z => t.inv ≫ z) hU).trans (t.inv_hom_id_assoc r))

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The right vertical map sends t : Hₙ(P) → M to b ∘ t ∘ Hₙ(f) : Hₙ(P′)
→ M′, with the canonical lift. -/
lemma homFixedCoefficientUniversalCoefficientSequenceMap_τ₃
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI').τ₃ =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        ((preadditiveYoneda.obj M).map (HomologicalComplex.homologyMap f n).op ≫
          (preadditiveYoneda.map b).app (op (P'.homology n))) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let S := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let T := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P' M' n hP' hI'
  let m : S ⟶ T := homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI'
  let a := HomologicalComplex.homologyMap (homFixedCoefficientMap f b) n
  let Γ := homFixedCoefficientRestriction P M n
  let Γ' := homFixedCoefficientRestriction P' M' n
  let t := (preadditiveYoneda.obj M).map (HomologicalComplex.homologyMap f n).op ≫
    (preadditiveYoneda.map b).app (op (P'.homology n))
  have hS := homFixedCoefficientUniversalCoefficientSequence_shortExact P M n hP hI
  letI : Epi S.g := hS.epi_g
  have hm : m.τ₂ = U.map a :=
    homFixedCoefficientUniversalCoefficientSequenceMap_τ₂ f b n hP hI hP' hI'
  have hg : S.g = U.map Γ := homFixedCoefficientUniversalCoefficientSequence_g P M n hP hI
  have hg' : T.g = U.map Γ' :=
    homFixedCoefficientUniversalCoefficientSequence_g P' M' n hP' hI'
  have hΓ : a ≫ Γ' = Γ ≫ t := homFixedCoefficientRestriction_naturality f b n
  have hStep : m.τ₂ ≫ T.g = U.map a ≫ U.map Γ' :=
    (congrArg (fun x : S.X₂ ⟶ T.X₂ => x ≫ T.g) hm).trans
      (congrArg (fun y : T.X₂ ⟶ T.X₃ => U.map a ≫ y) hg')
  have hComm : S.g ≫ m.τ₃ = m.τ₂ ≫ T.g := m.comm₂₃.symm
  have hFinal : U.map a ≫ U.map Γ' = S.g ≫ U.map t :=
    (U.map_comp a Γ').symm.trans
      ((congrArg U.map hΓ).trans
        ((U.map_comp Γ t).trans
          (congrArg (fun z => z ≫ U.map t) hg.symm)))
  apply (cancel_epi S.g).1
  change S.g ≫ m.τ₃ = S.g ≫ U.map t
  exact hComm.trans (hStep.trans hFinal)

/-- Let C be abelian with object universe u, morphism universe v and Ext groups in universe w. Let f
: P′ → P be an integer chain map, b : M → M′ a coefficient map and n ∈ ℤ. Assume every term and
every differential image of P and P′ is projective. The fixed-coefficient UCT terms are
Ext¹_C(Hₙ₋₁(P),M), Hⁿ Hom(P,M), and Hom_C(Hₙ(P),M), with canonical lifts to universe max(v,w),
and similarly for (P′,M′). The square formed by the positive left Ext injections commutes: the
injection for (P′,M′) after Ext pullback/pushforward equals Hⁿ Hom(f,b) after the injection for
(P,M). -/
@[reassoc]
lemma homFixedCoefficientUniversalCoefficientSequence_f_naturality
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1)))) :
    AddCommGrpCat.uliftFunctor.{v, w}.map
        (((extFunctor 1).map (HomologicalComplex.homologyMap f (n - 1)).op).app M ≫
          (extFunctorObj (P'.homology (n - 1)) 1).map b) ≫
        (homFixedCoefficientUniversalCoefficientSequence.{u, v, w}
          P' M' n hP' hI').f =
      (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI).f ≫
        AddCommGrpCat.uliftFunctor.{w, v}.map
          (HomologicalComplex.homologyMap (homFixedCoefficientMap f b) n) := by
  let S := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let T := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P' M' n hP' hI'
  let m : S ⟶ T := homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI'
  have h₁ := homFixedCoefficientUniversalCoefficientSequenceMap_τ₁ f b n hP hI hP' hI'
  have h₂ := homFixedCoefficientUniversalCoefficientSequenceMap_τ₂ f b n hP hI hP' hI'
  exact (congrArg (fun a => a ≫ T.f) h₁.symm).trans
    (m.comm₁₂.trans (congrArg (fun a => S.f ≫ a) h₂))

/-- Let C be abelian with Ext groups available, P an integer chain complex, M an object and n ∈ ℤ.
Assume every term and differential image of P is projective. The identity maps of P and M induce
the identity on the entire short exact sequence Ext¹(Hₙ₋₁(P),M) → Hⁿ Hom(P,M) → Hom(Hₙ(P),M). -/
lemma homFixedCoefficientUniversalCoefficientSequenceMap_id
    (P : ChainComplex C ℤ) (M : C) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1)))) :
    homFixedCoefficientUniversalCoefficientSequenceMap (𝟙 P) (𝟙 M) n hP hI hP hI =
      𝟙 (homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI) := by
  let S := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  have hS := homFixedCoefficientUniversalCoefficientSequence_shortExact P M n hP hI
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  apply ShortComplex.hom_ext_of_mono_f_of_epi_g
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n
  change (homFixedCoefficientUniversalCoefficientSequenceMap
    (𝟙 P) (𝟙 M) n hP hI hP hI).τ₂ = 𝟙 S.X₂
  exact (homFixedCoefficientUniversalCoefficientSequenceMap_τ₂
      (𝟙 P) (𝟙 M) n hP hI hP hI).trans
    ((congrArg (fun t => U.map (H.map t)) (homFixedCoefficientMap_id P M)).trans
      ((congrArg U.map (CategoryTheory.Functor.map_id H (homFixedCoefficient P M))).trans
        (CategoryTheory.Functor.map_id U (H.obj (homFixedCoefficient P M)))))

/-- Let C be abelian with Ext groups available. Let f : P′ → P, f′ : P″ → P′, b : M → M′ and b′ : M′
→ M″, and assume all terms and differential images of P,P′,P″ are projective. For every integer
n, the UCT map for (f ∘ f′,b′ ∘ b) is the composite of the map for (f,b) followed by that for
(f′,b′), on Ext¹, Hom cohomology and homology Hom. -/
lemma homFixedCoefficientUniversalCoefficientSequenceMap_comp
    {P'' : ChainComplex C ℤ} {M'' : C}
    (f : P' ⟶ P) (f' : P'' ⟶ P') (b : M ⟶ M') (b' : M' ⟶ M'') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p : ℤ, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p : ℤ, Projective (Abelian.image (P'.d p (p - 1))))
    (hP'' : ∀ p : ℤ, Projective (P''.X p))
    (hI'' : ∀ p : ℤ, Projective (Abelian.image (P''.d p (p - 1)))) :
    homFixedCoefficientUniversalCoefficientSequenceMap
        (f' ≫ f) (b ≫ b') n hP hI hP'' hI'' =
      homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI' ≫
        homFixedCoefficientUniversalCoefficientSequenceMap f' b' n hP' hI' hP'' hI'' := by
  let S := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P M n hP hI
  let T := homFixedCoefficientUniversalCoefficientSequence.{u, v, w} P'' M'' n hP'' hI''
  have hS := homFixedCoefficientUniversalCoefficientSequence_shortExact P M n hP hI
  have hT := homFixedCoefficientUniversalCoefficientSequence_shortExact P'' M'' n hP'' hI''
  letI : Epi S.g := hS.epi_g
  letI : Mono T.f := hT.mono_f
  apply ShortComplex.hom_ext_of_mono_f_of_epi_g
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n
  let a := homFixedCoefficientMap f b
  let a' := homFixedCoefficientMap f' b'
  have h₁ := homFixedCoefficientUniversalCoefficientSequenceMap_τ₂ f b n hP hI hP' hI'
  have h₂ := homFixedCoefficientUniversalCoefficientSequenceMap_τ₂ f' b' n hP' hI' hP'' hI''
  change (homFixedCoefficientUniversalCoefficientSequenceMap
    (f' ≫ f) (b ≫ b') n hP hI hP'' hI'').τ₂ =
      (homFixedCoefficientUniversalCoefficientSequenceMap f b n hP hI hP' hI').τ₂ ≫
        (homFixedCoefficientUniversalCoefficientSequenceMap f' b' n hP' hI' hP'' hI'').τ₂
  exact (homFixedCoefficientUniversalCoefficientSequenceMap_τ₂
      (f' ≫ f) (b ≫ b') n hP hI hP'' hI'').trans
    ((congrArg (fun t => U.map (H.map t)) (homFixedCoefficientMap_comp f f' b b')).trans
      ((congrArg U.map (H.map_comp a a')).trans
        ((U.map_comp (H.map a) (H.map a')).trans
          (congrArg₂ (fun x y => x ≫ y) h₁.symm h₂.symm))))

end ChainComplex
