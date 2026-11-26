/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ShortComplex.ExactSequence
public import MathlibExt.Algebra.Homology.ShortComplex.ChangeObjects
public import MathlibExt.Algebra.Homology.ChainComplex.HomCyclesConnecting
public import MathlibExt.CategoryTheory.Abelian.Ext.ProjectivePresentation
public import Mathlib.Algebra.Category.Grp.Ulift
public import MathlibExt.Algebra.Category.Grp.AddCommGrpProduct
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Universal coefficient sequences for full Hom cochain products

Let C be an abelian category, P an integer chain complex, Q an integer cochain complex, and n an
integer. Assume every term Pₚ and every differential image im(Pₚ → Pₚ₋₁) is projective. Then
there is a short exact sequence 0 → ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) → Hⁿ Hom(P,Q)   → ∏ₚ
Hom_C(Hₚ(P),H^{n-p}(Q)) → 0. The products range over all integers, and Q retains its
differential.

The sequence comes from 0 → Hom(I⁰(P),Q) → Hom(P,Q) → Hom(Z⁰(P),Q) → 0. The connecting map
identifies with (-1)^{n+1} times boundary precomposition. Normalizing this unit gives the
positive Yoneda Ext¹ cokernel and the Hom kernel obtained from the homology quotients. These
determine the left cohomology inclusion and right cycles restriction in the UCT sequence.

The Ext, object and morphism universes remain independent. Canonical group lifts compare the
three terms in a common universe. Pullback along a chain map P′ → P and pushforward along Q → Q′
give the simultaneous Ext, Hom cohomology and homology-Hom maps of short exact sequences.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex
open CategoryTheory.Abelian

universe u v w

namespace AddCommGrpCat

/-- Let Aₚ be a family of abelian groups indexed by all integers, in universe v. Moving groups to a
common universe max(v,w) commutes canonically with their dependent product: lift(∏ₚ Aₚ) ≅ ∏ₚ
lift(Aₚ). -/
def uliftIntPiIso (A : ℤ → AddCommGrpCat.{v}) :
    uliftFunctor.{w, v}.obj (AddCommGrpCat.of (∀ p : ℤ, A p)) ≅
      AddCommGrpCat.of (∀ p : ℤ, uliftFunctor.{w, v}.obj (A p)) :=
  uliftPiIso.{0, v, w} A

/-- For a family Aₚ of abelian groups in universe v, the common-universe product comparison sends a
lifted family k to the family of its lifted components: the p-th coordinate is lift(kₚ), for
every p ∈ ℤ. -/
lemma uliftIntPiIso_hom_up (A : ℤ → AddCommGrpCat.{v}) (k : ∀ p : ℤ, A p) (p : ℤ) :
    (uliftIntPiIso.{v, w} A).hom (ULift.up k) p = ULift.up (k p) := rfl

end AddCommGrpCat

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. For objects X,Y, the canonical isomorphism Hom_C(X,Y) ≅
Ext⁰_C(X,Y), f ↦ [f], remains an isomorphism after both groups are moved to universe max(v,w). -/
def homExtZeroLiftIso (X Y : C) :
    AddCommGrpCat.uliftFunctor.{w, v}.obj (AddCommGrpCat.of (X ⟶ Y)) ≅
      AddCommGrpCat.uliftFunctor.{v, w}.obj (AddCommGrpCat.of (Ext.{w} X Y 0)) :=
  (((AddEquiv.ulift : ULift.{w, v} (X ⟶ Y) ≃+ (X ⟶ Y)).trans Ext.addEquiv₀.symm).trans
    (AddEquiv.ulift : ULift.{v, w} (Ext.{w} X Y 0) ≃+ Ext.{w} X Y 0).symm).toAddCommGrpIso

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. For f : X → Y, the forward common-universe Hom–Ext⁰
comparison sends the lift of f to the lift of its degree-zero class Ext.mk₀(f). -/
lemma homExtZeroLiftIso_hom_up (X Y : C) (f : X ⟶ Y) :
    (homExtZeroLiftIso X Y).hom (ULift.up f) = ULift.up (Ext.mk₀ f) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. For f : X → Y, the inverse common-universe Hom–Ext⁰
comparison sends the lift of Ext.mk₀(f) back to the lift of f. -/
lemma homExtZeroLiftIso_inv_up (X Y : C) (f : X ⟶ Y) :
    (homExtZeroLiftIso X Y).inv (ULift.up (Ext.mk₀ f)) = ULift.up f := by
  change ULift.up (Ext.addEquiv₀ (Ext.mk₀ f)) = ULift.up f
  exact congrArg ULift.up (Ext.addEquiv₀.apply_symm_apply f)

end CategoryTheory.Abelian

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S S' : ShortComplex C}

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S be the short exact sequence 0 → S₁ → S₂ → S₃ → 0,
with inclusion a : S₁ → S₂, and let Y be an object. The positive Yoneda presentation is
Hom_C(S₂,Y) → Hom_C(S₁,Y) → Ext¹_C(S₃,Y). Its first map is precomposition with a and its second
sends t to the pushout t_*[S]. Canonical lifts put all terms in universe max(v,w). -/
def liftedHomPresentation (hS : S.ShortExact) (Y : C) :
    ShortComplex AddCommGrpCat.{max v w} := by
  let A : AddCommGrpCat.{max v w} := AddCommGrpCat.of (ULift.{w, v} (S.X₂ ⟶ Y))
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of (ULift.{w, v} (S.X₁ ⟶ Y))
  let D : AddCommGrpCat.{max v w} := AddCommGrpCat.of (ULift.{v, w} (Ext.{w} S.X₃ Y 1))
  let f : A ⟶ B :=
    AddCommGrpCat.uliftFunctor.{w, v}.map ((preadditiveYoneda.obj Y).map S.f.op)
  let g : B ⟶ D := (Abelian.homExtZeroLiftIso S.X₁ Y).hom ≫
    AddCommGrpCat.uliftFunctor.{v, w}.map (hS.extPresentationSequence Y).g
  refine ShortComplex.mk f g ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro k
  let k₀ : ULift.{w, v} (S.X₂ ⟶ Y) := k
  have hf : f.hom k₀ = ULift.up (S.f ≫ k₀.down) := rfl
  have hg : g.hom (ULift.up (S.f ≫ k₀.down)) =
      ULift.up (hS.extClass.comp (Ext.mk₀ (S.f ≫ k₀.down)) (add_zero 1)) := rfl
  have hMk : (Ext.mk₀ S.f).comp (Ext.mk₀ k₀.down) (zero_add 0) =
      Ext.mk₀ (S.f ≫ k₀.down) := Ext.mk₀_comp_mk₀ S.f k₀.down
  have hZero : hS.extClass.comp (Ext.mk₀ (S.f ≫ k₀.down)) (add_zero 1) = 0 :=
    (congrArg (fun e : Ext.{w} S.X₁ Y 0 => hS.extClass.comp e (add_zero 1)) hMk).symm.trans
      (hS.extClass_comp_assoc (Ext.mk₀ k₀.down))
  change (f ≫ g).hom k₀ = 0
  exact (AddCommGrpCat.comp_apply f g k₀).trans
    ((congrArg g.hom hf).trans
      (hg.trans (congrArg (fun e : Ext.{w} S.X₃ Y 1 => (ULift.up e : D)) hZero)))

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S be the short exact sequence 0 → S₁ → S₂ → S₃ → 0,
with inclusion a : S₁ → S₂, and let Y be an object. The ordinary Hom presentation Hom(S₂,Y) →
Hom(S₁,Y) → Ext¹(S₃,Y) is isomorphic to the degree-zero Ext presentation Ext⁰(S₂,Y) → Ext⁰(S₁,Y)
→ Ext¹(S₃,Y). The first two components use f ↦ Ext.mk₀(f), and the right component is the
identity on Ext¹, after common-universe transport. -/
def liftedHomPresentationIso (hS : S.ShortExact) (Y : C) :
    hS.liftedHomPresentation Y ≅
      (hS.extPresentationSequence Y).map AddCommGrpCat.uliftFunctor.{v, w} := by
  let R : ShortComplex AddCommGrpCat.{max v w} := hS.liftedHomPresentation Y
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    (hS.extPresentationSequence Y).map AddCommGrpCat.uliftFunctor.{v, w}
  let e₁ : R.X₁ ≅ T.X₁ := Abelian.homExtZeroLiftIso S.X₂ Y
  let e₂ : R.X₂ ≅ T.X₂ := Abelian.homExtZeroLiftIso S.X₁ Y
  refine ShortComplex.isoMk e₁ e₂ (Iso.refl _) ?_ ?_
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro k
    let k₀ : ULift.{w, v} (S.X₂ ⟶ Y) := k
    change ULift.up ((Ext.mk₀ S.f).comp (Ext.mk₀ k₀.down) (zero_add 0)) =
      ULift.up (Ext.mk₀ (S.f ≫ k₀.down))
    exact congrArg ULift.up (Ext.mk₀_comp_mk₀ S.f k₀.down)
  · let g : R.X₂ ⟶ T.X₃ := (Abelian.homExtZeroLiftIso S.X₁ Y).hom ≫
      AddCommGrpCat.uliftFunctor.{v, w}.map (hS.extPresentationSequence Y).g
    change g = g ≫ 𝟙 _
    exact (Category.comp_id g).symm

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S be the short exact sequence 0 → S₁ → S₂ → S₃ → 0,
with inclusion a : S₁ → S₂, and let Y be an object. The positive presentation Hom(S₂,Y) →
Hom(S₁,Y) → Ext¹(S₃,Y) is exact at Hom(S₁,Y). No projectivity of S₁ or S₃ is assumed. -/
lemma liftedHomPresentation_exact (hS : S.ShortExact) (Y : C) :
    (hS.liftedHomPresentation Y).Exact :=
  ShortComplex.exact_of_iso (hS.liftedHomPresentationIso Y).symm
    ((hS.extPresentationSequence_exact Y).map AddCommGrpCat.uliftFunctor.{v, w})

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S be the short exact sequence 0 → S₁ → S₂ → S₃ → 0,
with inclusion a : S₁ → S₂, and let Y be an object. If S₂ is projective, every class in
Ext¹_C(S₃,Y) is the pushout of [S] along a morphism S₁ → Y. Thus the positive connecting arrow
Hom(S₁,Y) → Ext¹(S₃,Y) is an epimorphism. -/
lemma liftedHomPresentation_epi (hS : S.ShortExact) (Y : C) [Projective S.X₂] :
    Epi (hS.liftedHomPresentation Y).g := by
  let T : ShortComplex AddCommGrpCat.{w} := hS.extPresentationSequence Y
  let U := AddCommGrpCat.uliftFunctor.{v, w}
  let e : AddCommGrpCat.of (ULift.{w, v} (S.X₁ ⟶ Y)) ≅
      U.obj (AddCommGrpCat.of (Ext.{w} S.X₁ Y 0)) :=
    Abelian.homExtZeroLiftIso S.X₁ Y
  letI : Epi T.g := hS.extPresentationSequence_epi Y
  have hU : Epi (U.map T.g) := U.map_epi T.g
  change Epi (e.hom ≫ U.map T.g)
  exact epi_comp' (inferInstance : Epi e.hom) hU

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S be the short exact sequence 0 → S₁ → S₂ → S₃ → 0,
with inclusion a : S₁ → S₂, and let Y be an object. The positive connecting arrow sends a lifted
morphism t : S₁ → Y to the lifted pushout class t_*[S] in Ext¹_C(S₃,Y), with no negative sign. -/
lemma liftedHomPresentation_g_apply (hS : S.ShortExact) (Y : C) (f : S.X₁ ⟶ Y) :
    (hS.liftedHomPresentation Y).g (ULift.up f) =
      ULift.up (hS.extClass.comp (Ext.mk₀ f) (add_zero 1)) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S and S′ be short exact sequences, φ : S′ → S a
morphism of sequences, and b : Y → Y′. There is an induced map from the positive Hom
presentation of (S,Y) to that of (S′,Y′): the two Hom components precompose with φ₂ and φ₁ and
postcompose with b, while the Ext¹ component pulls back along φ₃ and pushes forward along b. -/
def liftedHomPresentationMap (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') :
    hS.liftedHomPresentation Y ⟶ hS'.liftedHomPresentation Y' :=
  (hS.liftedHomPresentationIso Y).hom ≫
    AddCommGrpCat.uliftFunctor.{v, w}.mapShortComplex.map (hS.extPresentationMap hS' φ b) ≫
      (hS'.liftedHomPresentationIso Y').inv

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S and S′ be short exact sequences, φ : S′ → S a
morphism of sequences, and b : Y → Y′. On the first presentation term, a morphism t : S₂ → Y is
sent to b ∘ t ∘ φ₂ : S′₂ → Y′, with the same common-universe lift. -/
lemma liftedHomPresentationMap_τ₁_apply (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') (f : S.X₂ ⟶ Y) :
    (hS.liftedHomPresentationMap hS' φ b).τ₁ (ULift.up f) =
      ULift.up (φ.τ₂ ≫ f ≫ b) := by
  let a : S'.X₂ ⟶ S.X₂ := φ.τ₂
  let t : S'.X₂ ⟶ Y' := (a ≫ f) ≫ b
  have h₁ : ((Ext.mk₀ a).comp (Ext.mk₀ f) (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0) =
      Ext.mk₀ t :=
    (congrArg (fun e : Ext.{w} S'.X₂ Y 0 => e.comp (Ext.mk₀ b) (add_zero 0))
      (Ext.mk₀_comp_mk₀ a f)).trans (Ext.mk₀_comp_mk₀ (a ≫ f) b)
  have h₂ : Ext.addEquiv₀ (Ext.mk₀ t) = t :=
    (congrArg (fun e : Ext.{w} S'.X₂ Y' 0 => Ext.addEquiv₀ e)
      (Ext.addEquiv₀_symm_apply t)).symm.trans (Ext.addEquiv₀.apply_symm_apply t)
  change ULift.up (Ext.addEquiv₀
      (((Ext.mk₀ a).comp (Ext.mk₀ f) (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0))) =
    ULift.up (a ≫ f ≫ b)
  exact (congrArg (fun e : Ext.{w} S'.X₂ Y' 0 =>
    (ULift.up (Ext.addEquiv₀ e) : ULift.{w, v} (S'.X₂ ⟶ Y'))) h₁).trans
      ((congrArg ULift.up h₂).trans (congrArg ULift.up (Category.assoc a f b)))

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S and S′ be short exact sequences, φ : S′ → S a
morphism of sequences, and b : Y → Y′. On the middle presentation term, t : S₁ → Y is sent to b
∘ t ∘ φ₁ : S′₁ → Y′, with the same common-universe lift. -/
lemma liftedHomPresentationMap_τ₂_apply (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') (f : S.X₁ ⟶ Y) :
    (hS.liftedHomPresentationMap hS' φ b).τ₂ (ULift.up f) =
      ULift.up (φ.τ₁ ≫ f ≫ b) := by
  let a : S'.X₁ ⟶ S.X₁ := φ.τ₁
  let t : S'.X₁ ⟶ Y' := (a ≫ f) ≫ b
  have h₁ : ((Ext.mk₀ a).comp (Ext.mk₀ f) (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0) =
      Ext.mk₀ t :=
    (congrArg (fun e : Ext.{w} S'.X₁ Y 0 => e.comp (Ext.mk₀ b) (add_zero 0))
      (Ext.mk₀_comp_mk₀ a f)).trans (Ext.mk₀_comp_mk₀ (a ≫ f) b)
  have h₂ : Ext.addEquiv₀ (Ext.mk₀ t) = t :=
    (congrArg (fun e : Ext.{w} S'.X₁ Y' 0 => Ext.addEquiv₀ e)
      (Ext.addEquiv₀_symm_apply t)).symm.trans (Ext.addEquiv₀.apply_symm_apply t)
  change ULift.up (Ext.addEquiv₀
      (((Ext.mk₀ a).comp (Ext.mk₀ f) (zero_add 0)).comp (Ext.mk₀ b) (add_zero 0))) =
    ULift.up (a ≫ f ≫ b)
  exact (congrArg (fun e : Ext.{w} S'.X₁ Y' 0 =>
    (ULift.up (Ext.addEquiv₀ e) : ULift.{w, v} (S'.X₁ ⟶ Y'))) h₁).trans
      ((congrArg ULift.up h₂).trans (congrArg ULift.up (Category.assoc a f b)))

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let S and S′ be short exact sequences, φ : S′ → S a
morphism of sequences, and b : Y → Y′. The right component on Ext¹_C(S₃,Y) is pullback along φ₃
: S′₃ → S₃ followed by pushforward along b : Y → Y′. -/
lemma liftedHomPresentationMap_τ₃ (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S' ⟶ S) {Y Y' : C} (b : Y ⟶ Y') :
    (hS.liftedHomPresentationMap hS' φ b).τ₃ =
      AddCommGrpCat.uliftFunctor.{v, w}.map
        (((extFunctor 1).map φ.τ₃.op).app Y ≫ (extFunctorObj S'.X₃ 1).map b) := by
  let T : ShortComplex AddCommGrpCat.{w} := hS.extPresentationSequence Y
  let T' : ShortComplex AddCommGrpCat.{w} := hS'.extPresentationSequence Y'
  let U := AddCommGrpCat.uliftFunctor.{v, w}
  let ψ : T ⟶ T' := hS.extPresentationMap hS' φ b
  let r : T.X₃ ⟶ T'.X₃ :=
    ((extFunctor 1).map φ.τ₃.op).app Y ≫ (extFunctorObj S'.X₃ 1).map b
  have hψ : ψ.τ₃ = r := rfl
  have hmap : (U.mapShortComplex.map ψ).τ₃ = U.map ψ.τ₃ := rfl
  change (𝟙 _) ≫ (U.mapShortComplex.map ψ).τ₃ ≫ (𝟙 _) = U.map r
  exact (Category.id_comp ((U.mapShortComplex.map ψ).τ₃ ≫ 𝟙 _)).trans
    ((Category.comp_id (U.mapShortComplex.map ψ).τ₃).trans
      (hmap.trans (congrArg U.map hψ)))

end CategoryTheory.ShortComplex.ShortExact

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma prevDownInt (p : ℤ) : (ComplexShape.down ℤ).prev p = p + 1 :=
  (ComplexShape.down ℤ).prev_eq' (ComplexShape.down_mk _ _ (by omega))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. For each integer p, the
boundary–cycle–homology short complex is Bₚ → Zₚ → Hₚ, with maps βₚ and πₚ. -/
def homUctBoundaryPresentation (P : ChainComplex C ℤ) (p : ℤ) : ShortComplex C :=
  boundariesCyclesHomologySequence P (p + 1) p

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. For every p ∈ ℤ, the natural sequence 0 → Bₚ →
Zₚ → Hₚ → 0 is short exact; no splitting or projectivity is assumed. -/
lemma homUctBoundaryPresentation_shortExact (P : ChainComplex C ℤ) (p : ℤ) :
    (homUctBoundaryPresentation P p).ShortExact :=
  boundariesCyclesHomologySequence_shortExact P (p + 1) p (prevDownInt p)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. The first arrow of Bₚ → Zₚ → Hₚ is the
incoming differential-image inclusion βₚ, obtained from d_P^{p+1,p}. -/
lemma homUctBoundaryPresentation_f (P : ChainComplex C ℤ) (p : ℤ) :
    (homUctBoundaryPresentation P p).f = boundaryCyclesMap P (p + 1) p := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. The second arrow of Bₚ → Zₚ → Hₚ is the
canonical quotient πₚ from cycles to homology. -/
lemma homUctBoundaryPresentation_g (P : ChainComplex C ℤ) (p : ℤ) :
    (homUctBoundaryPresentation P p).g = P.homologyπ p := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. For an integer
chain map f : P′ → P and p ∈ ℤ, the incoming-boundary sequences for P′ and P form a morphism of
short exact sequences. Its components are the induced differential-image map, Zₚ(f), and Hₚ(f). -/
def homUctBoundaryPresentationMap {P P' : ChainComplex C ℤ} (f : P' ⟶ P) (p : ℤ) :
    homUctBoundaryPresentation P' p ⟶ homUctBoundaryPresentation P p :=
  (boundariesCyclesHomologySequenceFunctor (C := C) (c := ComplexShape.down ℤ)
    (p + 1) p).map f

/-- Let C be an abelian category with object universe u and morphism universe v. For f : P′ → P and
p ∈ ℤ, the cycle component of the induced boundary–cycle–homology presentation map is exactly
Zₚ(f) : Zₚ(P′) → Zₚ(P). -/
lemma homUctBoundaryPresentationMap_τ₂ {P P' : ChainComplex C ℤ} (f : P' ⟶ P) (p : ℤ) :
    (homUctBoundaryPresentationMap f p).τ₂ = HomologicalComplex.cyclesMap f p := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. For f : P′ → P and
p ∈ ℤ, the homology component of the induced boundary–cycle–homology presentation map is exactly
Hₚ(f) : Hₚ(P′) → Hₚ(P). -/
lemma homUctBoundaryPresentationMap_τ₃ {P P' : ChainComplex C ℤ} (f : P' ⟶ P) (p : ℤ) :
    (homUctBoundaryPresentationMap f p).τ₃ = HomologicalComplex.homologyMap f p := rfl

section ExtPresentation

variable [HasExt.{w} C]

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). For each p, the
corresponding row is Hom(Zₚ,Yₚ) → Hom(Bₚ,Yₚ) → Ext¹(Hₚ,Yₚ), using βₚ-precomposition and positive
pushout of the boundary extension. -/
def homUctPresentationRow (P : ChainComplex C ℤ) (Y : ℤ → C) (p : ℤ) :
    ShortComplex AddCommGrpCat.{max v w} :=
  (homUctBoundaryPresentation_shortExact P p).liftedHomPresentation (Y p)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The rows Hom(Zₚ,Yₚ) →
Hom(Bₚ,Yₚ) → Ext¹(Hₚ,Yₚ), for every p ∈ ℤ, form the discrete diagram whose limit is the full
product presentation. -/
def homUctPresentationRows (P : ChainComplex C ℤ) (Y : ℤ → C) :
    Discrete ℤ ⥤ ShortComplex AddCommGrpCat.{max v w} :=
  Discrete.functor (homUctPresentationRow P Y)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). Taking the limit of the
discrete diagram of positive presentation rows gives this full product short complex; its arrows
are the coordinatewise precomposition and positive Yoneda boundary maps. -/
def homUctPresentationLimit (P : ChainComplex C ℤ) (Y : ℤ → C) :
    ShortComplex AddCommGrpCat.{max v w} :=
  ShortComplex.limitShortComplex (homUctPresentationRows P Y)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The full product
presentation is exact at ∏ₚ Hom(Bₚ,Yₚ), because products of abelian groups preserve the
exactness of every positive Hom–Ext row. -/
lemma homUctPresentationLimit_exact (P : ChainComplex C ℤ) (Y : ℤ → C) :
    (homUctPresentationLimit P Y).Exact := by
  let R := homUctPresentationRows P Y
  let K := (ShortComplex.functorEquivalence (Discrete ℤ) AddCommGrpCat.{max v w}).inverse.obj R
  have hD : IsZero (R ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{max v w}) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply NatTrans.ext
    funext p
    exact (IsZero.iff_id_eq_zero _).1
      ((homUctPresentationRow P Y p.as).exact_iff_isZero_homology.mp
        ((homUctBoundaryPresentation_shortExact P p.as).liftedHomPresentation_exact (Y p.as)))
  have hK : K.Exact := K.exact_iff_isZero_homology.mpr
    ((ShortComplex.homologyDiagramIso R).isZero_iff.mpr hD)
  change (K.map (lim (J := Discrete ℤ) (C := AddCommGrpCat.{max v w}))).Exact
  exact hK.map (lim (J := Discrete ℤ) (C := AddCommGrpCat.{max v w}))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). If every Zₚ is
projective, the coordinatewise positive Yoneda maps are surjective and the product connecting
map ∏ₚ Hom(Bₚ,Yₚ) → ∏ₚ Ext¹(Hₚ,Yₚ) is an epimorphism. -/
lemma homUctPresentationLimit_epi (P : ChainComplex C ℤ) (Y : ℤ → C)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) : Epi (homUctPresentationLimit P Y).g := by
  let R := homUctPresentationRows P Y
  let K := (ShortComplex.functorEquivalence (Discrete ℤ) AddCommGrpCat.{max v w}).inverse.obj R
  letI : ∀ p : Discrete ℤ, Epi (K.g.app p) := fun p => by
    letI : Projective (homUctBoundaryPresentation P p.as).X₂ := by
      change Projective (P.cycles p.as)
      exact hZ p.as
    change Epi ((homUctBoundaryPresentation_shortExact P p.as).liftedHomPresentation
      (Y p.as)).g
    exact (homUctBoundaryPresentation_shortExact P p.as).liftedHomPresentation_epi (Y p.as)
  letI : Epi K.g := NatTrans.epi_of_epi_app K.g
  change Epi ((lim (J := Discrete ℤ) (C := AddCommGrpCat.{max v w})).map K.g)
  infer_instance

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The product short
complex uses precomposition with βₚ in its first arrow and tₚ ↦ (tₚ)_*[0 → Bₚ → Zₚ → Hₚ → 0] in
its second arrow, in each integer coordinate. -/
def homUctProductPresentation (P : ChainComplex C ℤ) (Y : ℤ → C) :
    ShortComplex AddCommGrpCat.{max v w} where
  X₁ := AddCommGrpCat.of (∀ p : ℤ, (homUctPresentationRow P Y p).X₁)
  X₂ := AddCommGrpCat.of (∀ p : ℤ, (homUctPresentationRow P Y p).X₂)
  X₃ := AddCommGrpCat.of (∀ p : ℤ, (homUctPresentationRow P Y p).X₃)
  f := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (homUctPresentationRow P Y p).f.hom)
  g := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (homUctPresentationRow P Y p).g.hom)
  zero := by
    let R := homUctPresentationRow P Y
    let A₁ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, (R p).X₁)
    let A₂ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, (R p).X₂)
    let A₃ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, (R p).X₃)
    let f : A₁ ⟶ A₂ := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (R p).f.hom)
    let g : A₂ ⟶ A₃ := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (R p).g.hom)
    apply AddCommGrpCat.ext
    intro k
    funext p
    have hRow : (R p).g.hom ((R p).f.hom (k p)) = 0 :=
      (AddCommGrpCat.comp_apply (R p).f (R p).g (k p)).symm.trans
        ((ConcreteCategory.congr_hom (R p).zero (k p)).trans
          (show (0 : (R p).X₁ ⟶ (R p).X₃).hom (k p) = 0 from rfl))
    change (f ≫ g).hom k p = 0
    exact (congrArg (fun x : A₃ => x p) (AddCommGrpCat.comp_apply f g k)).trans hRow

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). For each p ∈ ℤ,
evaluation at p is a morphism from the full product presentation to its degree-p Hom–Ext row, on
all three terms and both arrows. -/
def homUctProductPresentationProjection (P : ChainComplex C ℤ) (Y : ℤ → C) (p : ℤ) :
    homUctProductPresentation P Y ⟶ homUctPresentationRow P Y p := by
  let R : ℤ → ShortComplex AddCommGrpCat.{max v w} := homUctPresentationRow P Y
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let π₁ : A.X₁ ⟶ (R p).X₁ := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun q : ℤ => (R q).X₁) p)
  let π₂ : A.X₂ ⟶ (R p).X₂ := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun q : ℤ => (R q).X₂) p)
  let π₃ : A.X₃ ⟶ (R p).X₃ := AddCommGrpCat.ofHom
    (Pi.evalAddMonoidHom (fun q : ℤ => (R q).X₃) p)
  refine { τ₁ := π₁, τ₂ := π₂, τ₃ := π₃, comm₁₂ := ?_, comm₂₃ := ?_ }
  · apply AddCommGrpCat.ext
    intro k
    change (π₁ ≫ (R p).f).hom k = (A.f ≫ π₂).hom k
    rfl
  · apply AddCommGrpCat.ext
    intro k
    change (π₂ ≫ (R p).g).hom k = (A.g ≫ π₃).hom k
    rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The first arrow sends a
family (tₚ : Zₚ → Yₚ) to (tₚ ∘ βₚ : Bₚ → Yₚ), with the canonical lifts of these Hom groups. -/
lemma homUctProductPresentation_f_apply (P : ChainComplex C ℤ) (Y : ℤ → C)
    (k : (homUctProductPresentation P Y).X₁) (p : ℤ) :
    (homUctProductPresentation P Y).f k p =
      ULift.up (boundaryCyclesMap P (p + 1) p ≫ (k p).down) := by
  let k₀ : ∀ q : ℤ, ULift.{w, v} (P.cycles q ⟶ Y q) := k
  change ((homUctBoundaryPresentation_shortExact P p).liftedHomPresentation (Y p)).f.hom
    (k₀ p) = ULift.up (boundaryCyclesMap P (p + 1) p ≫ (k₀ p).down)
  rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The second arrow sends a
family tₚ : Bₚ → Yₚ to the positive pushout extension classes (tₚ)_*[0 → Bₚ → Zₚ → Hₚ → 0] in
every coordinate p. -/
lemma homUctProductPresentation_g_apply (P : ChainComplex C ℤ) (Y : ℤ → C)
    (k : (homUctProductPresentation P Y).X₂) (p : ℤ) :
    (homUctProductPresentation P Y).g k p =
      ULift.up ((homUctBoundaryPresentation_shortExact P p).extClass.comp
        (Ext.mk₀ (k p).down) (add_zero 1)) := by
  let S : ShortComplex C := homUctBoundaryPresentation P p
  let hS : S.ShortExact := homUctBoundaryPresentation_shortExact P p
  let k₀ : ∀ q : ℤ, ULift.{w, v} (Abelian.image (P.d (q + 1) q) ⟶ Y q) := k
  let v : ULift.{w, v} (S.X₁ ⟶ Y p) := k₀ p
  have hValue : ULift.up v.down = v := by cases v; rfl
  change (hS.liftedHomPresentation (Y p)).g.hom v =
    ULift.up (hS.extClass.comp (Ext.mk₀ v.down) (add_zero 1))
  exact (congrArg (hS.liftedHomPresentation (Y p)).g.hom hValue.symm).trans
    (hS.liftedHomPresentation_g_apply (Y p) v.down)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The limit of the
discrete presentation rows is canonically isomorphic, as a short complex, to their explicit full
product. The component comparisons preserve coordinate evaluation and both positive presentation
arrows. -/
def homUctPresentationLimitIso (P : ChainComplex C ℤ) (Y : ℤ → C) :
    homUctPresentationLimit P Y ≅ homUctProductPresentation P Y := by
  let R : Discrete ℤ ⥤ ShortComplex AddCommGrpCat.{max v w} := homUctPresentationRows P Y
  let L : ShortComplex AddCommGrpCat.{max v w} := homUctPresentationLimit P Y
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let e₁ : L.X₁ ≅ A.X₁ := AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₁)
  let e₂ : L.X₂ ≅ A.X₂ := AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₂)
  let e₃ : L.X₃ ≅ A.X₃ := AddCommGrpCat.intLimitIsoPi (R ⋙ ShortComplex.π₃)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · apply AddCommGrpCat.ext
    intro k
    funext p
    let π₁ : A.X₁ ⟶ (homUctPresentationRow P Y p).X₁ :=
      (homUctProductPresentationProjection P Y p).τ₁
    let π₂ : A.X₂ ⟶ (homUctPresentationRow P Y p).X₂ :=
      (homUctProductPresentationProjection P Y p).τ₂
    let l₁ : L.X₁ ⟶ (homUctPresentationRow P Y p).X₁ :=
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₁
    let l₂ : L.X₂ ⟶ (homUctPresentationRow P Y p).X₂ :=
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₂
    let f : (homUctPresentationRow P Y p).X₁ ⟶ (homUctPresentationRow P Y p).X₂ :=
      (homUctPresentationRow P Y p).f
    have h₁ : e₁.hom ≫ π₁ = l₁ :=
      (AddCommGrpCat.intLimitIsoPi_hom_eval (R ⋙ ShortComplex.π₁) p).trans
        (ShortComplex.limitShortComplexProjection_τ₁ R ⟨p⟩).symm
    have h₂ : e₂.hom ≫ π₂ = l₂ :=
      (AddCommGrpCat.intLimitIsoPi_hom_eval (R ⋙ ShortComplex.π₂) p).trans
        (ShortComplex.limitShortComplexProjection_τ₂ R ⟨p⟩).symm
    have hA : π₁ ≫ f = A.f ≫ π₂ := (homUctProductPresentationProjection P Y p).comm₁₂
    have hL : l₁ ≫ f = L.f ≫ l₂ := (ShortComplex.limitShortComplexProjection R ⟨p⟩).comm₁₂
    let a : L.X₁ ⟶ A.X₂ := e₁.hom ≫ A.f
    let b : L.X₁ ⟶ A.X₂ := L.f ≫ e₂.hom
    have hArrow : a ≫ π₂ = b ≫ π₂ :=
      (Category.assoc e₁.hom A.f π₂).trans
        ((congrArg (fun t => e₁.hom ≫ t) hA.symm).trans
          ((Category.assoc e₁.hom π₁ f).symm.trans
            ((congrArg (fun t => t ≫ f) h₁).trans
              (hL.trans ((congrArg (fun t => L.f ≫ t) h₂.symm).trans
                (Category.assoc L.f e₂.hom π₂).symm)))))
    have hLeft : (a ≫ π₂).hom k = a.hom k p := AddCommGrpCat.comp_apply a π₂ k
    have hRight : (b ≫ π₂).hom k = b.hom k p := AddCommGrpCat.comp_apply b π₂ k
    change a.hom k p = b.hom k p
    exact hLeft.symm.trans ((ConcreteCategory.congr_hom hArrow k).trans hRight)
  · apply AddCommGrpCat.ext
    intro k
    funext p
    let π₂ : A.X₂ ⟶ (homUctPresentationRow P Y p).X₂ :=
      (homUctProductPresentationProjection P Y p).τ₂
    let π₃ : A.X₃ ⟶ (homUctPresentationRow P Y p).X₃ :=
      (homUctProductPresentationProjection P Y p).τ₃
    let l₂ : L.X₂ ⟶ (homUctPresentationRow P Y p).X₂ :=
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₂
    let l₃ : L.X₃ ⟶ (homUctPresentationRow P Y p).X₃ :=
      (ShortComplex.limitShortComplexProjection R ⟨p⟩).τ₃
    let g : (homUctPresentationRow P Y p).X₂ ⟶ (homUctPresentationRow P Y p).X₃ :=
      (homUctPresentationRow P Y p).g
    have h₂ : e₂.hom ≫ π₂ = l₂ :=
      (AddCommGrpCat.intLimitIsoPi_hom_eval (R ⋙ ShortComplex.π₂) p).trans
        (ShortComplex.limitShortComplexProjection_τ₂ R ⟨p⟩).symm
    have h₃ : e₃.hom ≫ π₃ = l₃ :=
      (AddCommGrpCat.intLimitIsoPi_hom_eval (R ⋙ ShortComplex.π₃) p).trans
        (ShortComplex.limitShortComplexProjection_τ₃ R ⟨p⟩).symm
    have hA : π₂ ≫ g = A.g ≫ π₃ := (homUctProductPresentationProjection P Y p).comm₂₃
    have hL : l₂ ≫ g = L.g ≫ l₃ := (ShortComplex.limitShortComplexProjection R ⟨p⟩).comm₂₃
    let a : L.X₂ ⟶ A.X₃ := e₂.hom ≫ A.g
    let b : L.X₂ ⟶ A.X₃ := L.g ≫ e₃.hom
    have hArrow : a ≫ π₃ = b ≫ π₃ :=
      (Category.assoc e₂.hom A.g π₃).trans
        ((congrArg (fun t => e₂.hom ≫ t) hA.symm).trans
          ((Category.assoc e₂.hom π₂ g).symm.trans
            ((congrArg (fun t => t ≫ g) h₂).trans
              (hL.trans ((congrArg (fun t => L.g ≫ t) h₃.symm).trans
                (Category.assoc L.g e₃.hom π₃).symm)))))
    have hLeft : (a ≫ π₃).hom k = a.hom k p := AddCommGrpCat.comp_apply a π₃ k
    have hRight : (b ≫ π₃).hom k = b.hom k p := AddCommGrpCat.comp_apply b π₃ k
    change a.hom k p = b.hom k p
    exact hLeft.symm.trans ((ConcreteCategory.congr_hom hArrow k).trans hRight)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The explicit full
product short complex is exact at ∏ₚ Hom(Bₚ,Yₚ); its kernel is the product of the kernels in the
individual positive presentation rows. -/
lemma homUctProductPresentation_exact (P : ChainComplex C ℤ) (Y : ℤ → C) :
    (homUctProductPresentation P Y).Exact :=
  ShortComplex.exact_of_iso (homUctPresentationLimitIso P Y)
    (homUctPresentationLimit_exact P Y)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). If every cycle object Zₚ
is projective, the positive product connecting arrow to ∏ₚ Ext¹(Hₚ,Yₚ) is an epimorphism. -/
lemma homUctProductPresentation_epi (P : ChainComplex C ℤ) (Y : ℤ → C)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) : Epi (homUctProductPresentation P Y).g := by
  let L : ShortComplex AddCommGrpCat.{max v w} := homUctPresentationLimit P Y
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let e : L ≅ A := homUctPresentationLimitIso P Y
  let a : L.X₂ ⟶ A.X₂ := e.hom.τ₂
  let b : L.X₃ ⟶ A.X₃ := e.hom.τ₃
  letI : Epi L.g := homUctPresentationLimit_epi P Y hZ
  have h : a ≫ A.g = L.g ≫ b := e.hom.comm₂₃
  letI : Epi (a ≫ A.g) := by
    rw [h]
    infer_instance
  exact epi_of_epi a A.g

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). Assume every Zₚ is
projective. The cokernel of β-precomposition ∏ₚ Hom(Zₚ,Yₚ) → ∏ₚ Hom(Bₚ,Yₚ) is canonically
isomorphic to ∏ₚ Ext¹(Hₚ,Yₚ), with the positive Yoneda boundary map as quotient comparison. -/
def homUctPresentationCokernelIso (P : ChainComplex C ℤ) (Y : ℤ → C)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    cokernel (homUctProductPresentation P Y).f ≅ (homUctProductPresentation P Y).X₃ := by
  letI := homUctProductPresentation_epi P Y hZ
  exact (cokernelIsCokernel (homUctProductPresentation P Y).f).coconePointUniqueUpToIso
    (homUctProductPresentation_exact P Y).gIsCokernel

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). Assume every Zₚ is
projective. If α is the cokernel-to-product-Ext¹ isomorphism, then the cokernel quotient
followed by α equals the positive product Yoneda connecting map. -/
@[reassoc]
lemma homUctPresentationCokernelIso_π_hom (P : ChainComplex C ℤ) (Y : ℤ → C)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    cokernel.π (homUctProductPresentation P Y).f ≫
        (homUctPresentationCokernelIso P Y hZ).hom = (homUctProductPresentation P Y).g := by
  letI := homUctProductPresentation_epi P Y hZ
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (homUctProductPresentation P Y).f)
    (homUctProductPresentation_exact P Y).gIsCokernel WalkingParallelPair.one

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). Assume every Zₚ is
projective. The cokernel class of a family tₚ : Bₚ → Yₚ is sent in degree p to the positive
pushout class (tₚ)_*[0 → Bₚ → Zₚ → Hₚ → 0]. -/
lemma homUctPresentationCokernelIso_apply (P : ChainComplex C ℤ) (Y : ℤ → C)
    (hZ : ∀ p : ℤ, Projective (P.cycles p))
    (k : (homUctProductPresentation P Y).X₂) (p : ℤ) :
    (homUctPresentationCokernelIso P Y hZ).hom
        (cokernel.π (homUctProductPresentation P Y).f k) p =
      ULift.up ((homUctBoundaryPresentation_shortExact P p).extClass.comp
        (Ext.mk₀ (k p).down) (add_zero 1)) := by
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let e : cokernel A.f ≅ A.X₃ := homUctPresentationCokernelIso P Y hZ
  let π : A.X₂ ⟶ cokernel A.f := cokernel.π A.f
  have h : π ≫ e.hom = A.g := homUctPresentationCokernelIso_π_hom P Y hZ
  have hValue : e.hom.hom (π.hom k) = A.g.hom k :=
    (AddCommGrpCat.comp_apply π e.hom k).symm.trans (ConcreteCategory.congr_hom h k)
  exact (congrArg (fun z : A.X₃ => z p) hValue).trans
    (homUctProductPresentation_g_apply P Y k p)

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. The full Hom–Ext presentation for (P,Y) maps to that for
(P′,Y′). Each Hom component precomposes with the induced cycle or boundary map and postcomposes
with bₚ; each Ext¹ component is pullback along Hₚ(f) followed by pushforward along bₚ. -/
def homUctProductPresentationMap {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    homUctProductPresentation P Y ⟶ homUctProductPresentation P' Y' := by
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let B : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P' Y'
  let φ (p : ℤ) : homUctPresentationRow P Y p ⟶ homUctPresentationRow P' Y' p :=
    (homUctBoundaryPresentation_shortExact P p).liftedHomPresentationMap
      (homUctBoundaryPresentation_shortExact P' p) (homUctBoundaryPresentationMap f p) (b p)
  let a : A.X₁ ⟶ B.X₁ := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (φ p).τ₁.hom)
  let c : A.X₂ ⟶ B.X₂ := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (φ p).τ₂.hom)
  let d : A.X₃ ⟶ B.X₃ := AddCommGrpCat.ofHom (AddMonoidHom.piMap fun p => (φ p).τ₃.hom)
  refine { τ₁ := a, τ₂ := c, τ₃ := d, comm₁₂ := ?_, comm₂₃ := ?_ }
  · apply AddCommGrpCat.ext
    intro k
    funext p
    have hValue := ConcreteCategory.congr_hom (φ p).comm₁₂ (k p)
    have hLeft := AddCommGrpCat.comp_apply a B.f k
    have hRight := AddCommGrpCat.comp_apply A.f c k
    change (a ≫ B.f).hom k p = (A.f ≫ c).hom k p
    exact (congrArg (fun z : B.X₂ => z p) hLeft).trans
      (hValue.trans (congrArg (fun z : B.X₂ => z p) hRight).symm)
  · apply AddCommGrpCat.ext
    intro k
    funext p
    have hValue := ConcreteCategory.congr_hom (φ p).comm₂₃ (k p)
    have hLeft := AddCommGrpCat.comp_apply c B.g k
    have hRight := AddCommGrpCat.comp_apply A.g d k
    change (c ≫ B.g).hom k p = (A.g ≫ d).hom k p
    exact (congrArg (fun z : B.X₃ => z p) hLeft).trans
      (hValue.trans (congrArg (fun z : B.X₃ => z p) hRight).symm)

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. A family tₚ : Zₚ → Yₚ in the first term is sent to bₚ ∘ tₚ ∘
Zₚ(f) : Z′ₚ → Y′ₚ. -/
lemma homUctProductPresentationMap_τ₁_apply {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p)
    (k : (homUctProductPresentation P Y).X₁) (p : ℤ) :
    (homUctProductPresentationMap f b).τ₁ k p =
      ULift.up (HomologicalComplex.cyclesMap f p ≫ (k p).down ≫ b p) := by
  let S : ShortComplex C := homUctBoundaryPresentation P p
  let S' : ShortComplex C := homUctBoundaryPresentation P' p
  let hS : S.ShortExact := homUctBoundaryPresentation_shortExact P p
  let hS' : S'.ShortExact := homUctBoundaryPresentation_shortExact P' p
  let φ : S' ⟶ S := homUctBoundaryPresentationMap f p
  let k₀ : ∀ q : ℤ, ULift.{w, v} (P.cycles q ⟶ Y q) := k
  let v : ULift.{w, v} (S.X₂ ⟶ Y p) := k₀ p
  have hValue : ULift.up v.down = v := by cases v; rfl
  have hφ : φ.τ₂ = HomologicalComplex.cyclesMap f p :=
    homUctBoundaryPresentationMap_τ₂ f p
  change (hS.liftedHomPresentationMap hS' φ (b p)).τ₁.hom v =
    ULift.up (HomologicalComplex.cyclesMap f p ≫ v.down ≫ b p)
  exact (congrArg (hS.liftedHomPresentationMap hS' φ (b p)).τ₁.hom hValue.symm).trans
    ((hS.liftedHomPresentationMap_τ₁_apply hS' φ (b p) v.down).trans
      (congrArg (fun a : S'.X₂ ⟶ S.X₂ => ULift.up (a ≫ v.down ≫ b p)) hφ))

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. A family tₚ : Bₚ → Yₚ in the middle term is sent to bₚ ∘ tₚ
∘ Bₚ(f) : B′ₚ → Y′ₚ, where Bₚ(f) is the actual induced differential-image map. -/
lemma homUctProductPresentationMap_τ₂_apply {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p)
    (k : (homUctProductPresentation P Y).X₂) (p : ℤ) :
    (homUctProductPresentationMap f b).τ₂ k p =
      ULift.up ((homUctBoundaryPresentationMap f p).τ₁ ≫ (k p).down ≫ b p) := by
  let S : ShortComplex C := homUctBoundaryPresentation P p
  let S' : ShortComplex C := homUctBoundaryPresentation P' p
  let hS : S.ShortExact := homUctBoundaryPresentation_shortExact P p
  let hS' : S'.ShortExact := homUctBoundaryPresentation_shortExact P' p
  let φ : S' ⟶ S := homUctBoundaryPresentationMap f p
  let k₀ : ∀ q : ℤ, ULift.{w, v} (Abelian.image (P.d (q + 1) q) ⟶ Y q) := k
  let v : ULift.{w, v} (S.X₁ ⟶ Y p) := k₀ p
  have hValue : ULift.up v.down = v := by cases v; rfl
  change (hS.liftedHomPresentationMap hS' φ (b p)).τ₂.hom v =
    ULift.up (φ.τ₁ ≫ v.down ≫ b p)
  exact (congrArg (hS.liftedHomPresentationMap hS' φ (b p)).τ₂.hom hValue.symm).trans
    (hS.liftedHomPresentationMap_τ₂_apply hS' φ (b p) v.down)

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. A family eₚ ∈ Ext¹_C(Hₚ,Yₚ) is sent to (bₚ)_*(Hₚ(f))^* eₚ in
Ext¹_C(H′ₚ,Y′ₚ), with no additional sign. -/
lemma homUctProductPresentationMap_τ₃_apply {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p)
    (e : (homUctProductPresentation P Y).X₃) (p : ℤ) :
    (homUctProductPresentationMap f b).τ₃ e p =
      ULift.up (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e p).down
        (zero_add 1)).comp (Ext.mk₀ (b p)) (add_zero 1)) := by
  let S : ShortComplex C := homUctBoundaryPresentation P p
  let S' : ShortComplex C := homUctBoundaryPresentation P' p
  let hS : S.ShortExact := homUctBoundaryPresentation_shortExact P p
  let hS' : S'.ShortExact := homUctBoundaryPresentation_shortExact P' p
  let φ : S' ⟶ S := homUctBoundaryPresentationMap f p
  let e₀ : ∀ q : ℤ, ULift.{v, w} (Ext.{w} (P.homology q) (Y q) 1) := e
  let v : ULift.{v, w} (Ext.{w} S.X₃ (Y p) 1) := e₀ p
  let A : AddCommGrpCat.{max v w} := AddCommGrpCat.of (ULift.{v, w} (Ext.{w} S.X₃ (Y p) 1))
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of (ULift.{v, w} (Ext.{w} S'.X₃ (Y' p) 1))
  let U : AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max v w} := AddCommGrpCat.uliftFunctor.{v, w}
  let a : A ⟶ B := (hS.liftedHomPresentationMap hS' φ (b p)).τ₃
  let b' : A ⟶ B := U.map (((extFunctor 1).map φ.τ₃.op).app (Y p) ≫
    (extFunctorObj S'.X₃ 1).map (b p))
  have h : a = b' := hS.liftedHomPresentationMap_τ₃ hS' φ (b p)
  change a.hom v = ULift.up (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp v.down
    (zero_add 1)).comp (Ext.mk₀ (b p)) (add_zero 1))
  have hValue : b'.hom v = ULift.up (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp v.down
      (zero_add 1)).comp (Ext.mk₀ (b p)) (add_zero 1)) := rfl
  exact (congrArg (fun m : A ⟶ B => m.hom v) h).trans hValue

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. The commuting square of the two β-precomposition arrows
induces a map between their cokernels, from the presentation of (P,Y) to that of (P′,Y′). -/
def homUctPresentationCokernelMap {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    cokernel (homUctProductPresentation P Y).f ⟶
      cokernel (homUctProductPresentation P' Y').f :=
  cokernel.map _ _ (homUctProductPresentationMap f b).τ₁
    (homUctProductPresentationMap f b).τ₂ (homUctProductPresentationMap f b).comm₁₂.symm

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. Assume the cycles Zₚ and Z′ₚ are projective in every degree.
The cokernel-to-product-Ext¹ comparisons commute with the induced cokernel map and the
coordinatewise Ext pullback/pushforward map. -/
lemma homUctPresentationCokernelIso_naturality {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) (hZ' : ∀ p : ℤ, Projective (P'.cycles p)) :
    homUctPresentationCokernelMap f b ≫ (homUctPresentationCokernelIso P' Y' hZ').hom =
      (homUctPresentationCokernelIso P Y hZ).hom ≫
        (homUctProductPresentationMap f b).τ₃ := by
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let B : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P' Y'
  let φ : A ⟶ B := homUctProductPresentationMap f b
  let π : A.X₂ ⟶ cokernel A.f := cokernel.π A.f
  let π' : B.X₂ ⟶ cokernel B.f := cokernel.π B.f
  let m : cokernel A.f ⟶ cokernel B.f := homUctPresentationCokernelMap f b
  let e : cokernel A.f ≅ A.X₃ := homUctPresentationCokernelIso P Y hZ
  let e' : cokernel B.f ≅ B.X₃ := homUctPresentationCokernelIso P' Y' hZ'
  have hm : π ≫ m = φ.τ₂ ≫ π' := by
    dsimp only [m, homUctPresentationCokernelMap, cokernel.map]
    exact cokernel.π_desc _ _ _
  have he : π ≫ e.hom = A.g := homUctPresentationCokernelIso_π_hom P Y hZ
  have he' : π' ≫ e'.hom = B.g := homUctPresentationCokernelIso_π_hom P' Y' hZ'
  have hφ : φ.τ₂ ≫ B.g = A.g ≫ φ.τ₃ := φ.comm₂₃
  apply (cancel_epi π).1
  change π ≫ (m ≫ e'.hom) = π ≫ (e.hom ≫ φ.τ₃)
  calc
    _ = (π ≫ m) ≫ e'.hom := (Category.assoc _ _ _).symm
    _ = (φ.τ₂ ≫ π') ≫ e'.hom := congrArg (fun a => a ≫ e'.hom) hm
    _ = φ.τ₂ ≫ (π' ≫ e'.hom) := Category.assoc _ _ _
    _ = φ.τ₂ ≫ B.g := congrArg (fun a => φ.τ₂ ≫ a) he'
    _ = A.g ≫ φ.τ₃ := hφ
    _ = (π ≫ e.hom) ≫ φ.τ₃ := congrArg (fun a => a ≫ φ.τ₃) he.symm
    _ = π ≫ (e.hom ≫ φ.τ₃) := Category.assoc _ _ _

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The product ∏ₚ
Hom(Hₚ,Yₚ) maps into ∏ₚ Hom(Zₚ,Yₚ) by precomposition with each homology quotient πₚ. Its p-th
coordinate sends tₚ to tₚ ∘ πₚ. -/
def homUctHomKernelInclusion (P : ChainComplex C ℤ) (Y : ℤ → C) :
    AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p)) ⟶
      (homUctProductPresentation P Y).X₁ := by
  let f (p : ℤ) : ULift.{w, v} (P.homology p ⟶ Y p) →+
      ULift.{w, v} (P.cycles p ⟶ Y p) :=
    AddMonoidHom.mk' (fun k => ULift.up (P.homologyπ p ≫ k.down)) (by
      intro k k'
      apply ULift.ext
      change P.homologyπ p ≫ (k.down + k'.down) =
        P.homologyπ p ≫ k.down + P.homologyπ p ≫ k'.down
      exact Preadditive.comp_add (P.cycles p) (P.homology p) (Y p)
        (P.homologyπ p) k.down k'.down)
  exact AddCommGrpCat.ofHom (AddMonoidHom.piMap f)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). Precomposition by πₚ
followed by precomposition by βₚ is zero in every degree, since πₚ ∘ βₚ=0. Thus the full
homology-Hom inclusion is killed by the first product-presentation arrow. -/
@[reassoc]
lemma homUctHomKernelInclusion_f (P : ChainComplex C ℤ) (Y : ℤ → C) :
    homUctHomKernelInclusion P Y ≫ (homUctProductPresentation P Y).f = 0 := by
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p))
  let κ : B ⟶ A.X₁ := homUctHomKernelInclusion P Y
  apply AddCommGrpCat.ext
  intro k
  funext p
  let v : P.homology p ⟶ Y p := (k p).down
  let a : Abelian.image (P.d (p + 1) p) ⟶ P.cycles p := boundaryCyclesMap P (p + 1) p
  let π : P.cycles p ⟶ P.homology p := P.homologyπ p
  have hZero : a ≫ (π ≫ v) = 0 :=
    (Category.assoc a π v).symm.trans
      ((congrArg (fun t : Abelian.image (P.d (p + 1) p) ⟶ P.homology p => t ≫ v)
        (boundaryCyclesMap_homologyπ P (p + 1) p)).trans Limits.zero_comp)
  have hValue : (A.f.hom (κ.hom k)) p = ULift.up (a ≫ (π ≫ v)) := rfl
  change (κ ≫ A.f).hom k p = 0
  exact (congrArg (fun z : A.X₂ => z p) (AddCommGrpCat.comp_apply κ A.f k)).trans
    (hValue.trans ((congrArg (fun t : Abelian.image (P.d (p + 1) p) ⟶ Y p =>
      (ULift.up t : ULift.{w, v} (Abelian.image (P.d (p + 1) p) ⟶ Y p))) hZero).trans rfl))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The map ∏ₚ Hom(Hₚ,Yₚ) →
∏ₚ Hom(Zₚ,Yₚ), tₚ ↦ tₚ ∘ πₚ, is a monomorphism because every homology quotient πₚ is an
epimorphism. -/
lemma homUctHomKernelInclusion_mono (P : ChainComplex C ℤ) (Y : ℤ → C) :
    Mono (homUctHomKernelInclusion P Y) := by
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p))
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let κ : B ⟶ A.X₁ := homUctHomKernelInclusion P Y
  apply (AddCommGrpCat.mono_iff_injective κ).2
  intro k k' h
  change κ.hom k = κ.hom k' at h
  funext p
  apply ULift.ext
  apply (cancel_epi (P.homologyπ p)).1
  have hValue : ULift.up (P.homologyπ p ≫ (k p).down) =
      (ULift.up (P.homologyπ p ≫ (k' p).down) :
        ULift.{w, v} (P.cycles p ⟶ Y p)) := congrFun h p
  exact congrArg (fun v : ULift.{w, v} (P.cycles p ⟶ Y p) => v.down) hValue

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The inclusion ∏ₚ
Hom(Hₚ,Yₚ) → ∏ₚ Hom(Zₚ,Yₚ) is a kernel of the β-precomposition map to ∏ₚ Hom(Bₚ,Yₚ). This is the
full product of the contravariant Hom kernels of 0 → Bₚ → Zₚ → Hₚ → 0. -/
def homUctHomKernelIsKernel (P : ChainComplex C ℤ) (Y : ℤ → C) :
    IsLimit (KernelFork.ofι (homUctHomKernelInclusion P Y)
      (homUctHomKernelInclusion_f P Y)) := by
  let A : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p))
  let κ : B ⟶ A.X₁ := homUctHomKernelInclusion P Y
  letI : Mono κ := homUctHomKernelInclusion_mono P Y
  apply KernelFork.IsLimit.ofι' κ (homUctHomKernelInclusion_f P Y)
  intro W k hk
  let row (p : ℤ) : ShortComplex AddCommGrpCat.{max v w} :=
    (homUctBoundaryPresentation P p).op.map
      (preadditiveYoneda.obj (Y p) ⋙ AddCommGrpCat.uliftFunctor.{w, v})
  let hRow (p : ℤ) : IsLimit (KernelFork.ofι (row p).f (row p).zero) :=
    KernelFork.mapIsLimit _ (homUctBoundaryPresentation_shortExact P p).op.fIsKernel
      (preadditiveYoneda.obj (Y p) ⋙ AddCommGrpCat.uliftFunctor.{w, v})
  let π₁ (p : ℤ) : A.X₁ ⟶ (row p).X₂ :=
    (homUctProductPresentationProjection P Y p).τ₁
  let kRow (p : ℤ) : W ⟶ (row p).X₂ := k ≫ π₁ p
  have hkRow (p : ℤ) : kRow p ≫ (row p).g = 0 := by
    apply AddCommGrpCat.ext
    intro x
    have hkValue : A.f.hom (k.hom x) = 0 :=
      (AddCommGrpCat.comp_apply k A.f x).symm.trans
        ((ConcreteCategory.congr_hom hk x).trans (show (0 : W ⟶ A.X₂).hom x = 0 from rfl))
    have hProjection : (kRow p).hom x = k.hom x p := AddCommGrpCat.comp_apply k (π₁ p) x
    have hValue : (row p).g.hom (k.hom x p) = A.f.hom (k.hom x) p := rfl
    change (kRow p ≫ (row p).g).hom x = 0
    exact (AddCommGrpCat.comp_apply (kRow p) (row p).g x).trans
      ((congrArg (row p).g.hom hProjection).trans
        (hValue.trans (congrArg (fun z : A.X₂ => z p) hkValue)))
  let lRow (p : ℤ) : W ⟶ (row p).X₁ :=
    (hRow p).lift (KernelFork.ofι (kRow p) (hkRow p))
  let l : W ⟶ B := AddCommGrpCat.ofHom (AddMonoidHom.pi fun p => (lRow p).hom)
  refine ⟨l, ?_⟩
  apply AddCommGrpCat.ext
  intro x
  funext p
  have hLift : lRow p ≫ (row p).f = kRow p :=
    Fork.IsLimit.lift_ι (t := KernelFork.ofι (kRow p) (hkRow p)) (hRow p)
  have hLeft : (l ≫ κ).hom x p = (row p).f.hom ((lRow p).hom x) :=
    congrArg (fun z : A.X₁ => z p) (AddCommGrpCat.comp_apply l κ x)
  have hRowValue : (lRow p ≫ (row p).f).hom x =
      (row p).f.hom ((lRow p).hom x) := AddCommGrpCat.comp_apply (lRow p) (row p).f x
  have hProjection : (kRow p).hom x = k.hom x p := AddCommGrpCat.comp_apply k (π₁ p) x
  change (l ≫ κ).hom x p = k.hom x p
  exact hLeft.trans (hRowValue.symm.trans
    ((ConcreteCategory.congr_hom hLift x).trans hProjection))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The kernel of ∏ₚ
Hom(Zₚ,Yₚ) → ∏ₚ Hom(Bₚ,Yₚ) is canonically isomorphic to ∏ₚ Hom(Hₚ,Yₚ), with inverse represented
by precomposition with the homology quotients πₚ. -/
def homUctHomKernelIso (P : ChainComplex C ℤ) (Y : ℤ → C) :
    kernel (homUctProductPresentation P Y).f ≅
      AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p)) :=
  (kernelIsKernel (homUctProductPresentation P Y).f).conePointUniqueUpToIso
    (homUctHomKernelIsKernel P Y)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The
kernel-to-product-Hom comparison followed by the πₚ-precomposition inclusion equals the canonical
inclusion of the presentation kernel. -/
@[reassoc]
lemma homUctHomKernelIso_hom_inclusion (P : ChainComplex C ℤ) (Y : ℤ → C) :
    (homUctHomKernelIso P Y).hom ≫ homUctHomKernelInclusion P Y =
      kernel.ι (homUctProductPresentation P Y).f :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (kernelIsKernel (homUctProductPresentation P Y).f)
    (homUctHomKernelIsKernel P Y) WalkingParallelPair.zero

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an
integer-indexed chain complex. Put Bₚ=im(d_P : Pₚ₊₁ → Pₚ), Zₚ=Zₚ(P), and Hₚ=Hₚ(P), with boundary
inclusion βₚ : Bₚ → Zₚ and quotient πₚ : Zₚ → Hₚ. Let Y : ℤ → C be a coefficient family and
assume Ext_C is available in universe w. The full presentation has terms ∏ₚ Hom_C(Zₚ,Yₚ) → ∏ₚ
Hom_C(Bₚ,Yₚ) → ∏ₚ Ext¹_C(Hₚ,Yₚ), in the common group universe max(v,w). The inverse
product-Hom-to-kernel comparison followed by the kernel inclusion is exactly (tₚ) ↦ (tₚ ∘ πₚ). -/
@[reassoc]
lemma homUctHomKernelIso_inv_ι (P : ChainComplex C ℤ) (Y : ℤ → C) :
    (homUctHomKernelIso P Y).inv ≫ kernel.ι (homUctProductPresentation P Y).f =
      homUctHomKernelInclusion P Y :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (kernelIsKernel (homUctProductPresentation P Y).f)
    (homUctHomKernelIsKernel P Y) WalkingParallelPair.zero

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. There is an additive map ∏ₚ Hom(Hₚ,Yₚ) → ∏ₚ Hom(H′ₚ,Y′ₚ),
sending tₚ to bₚ ∘ tₚ ∘ Hₚ(f) in each integer coordinate. -/
def homUctHomProductMap {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p)) ⟶
      AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P'.homology p ⟶ Y' p)) := by
  let m (p : ℤ) : ULift.{w, v} (P.homology p ⟶ Y p) →+
      ULift.{w, v} (P'.homology p ⟶ Y' p) :=
    AddMonoidHom.mk' (fun k => ULift.up (HomologicalComplex.homologyMap f p ≫ k.down ≫ b p)) (by
      intro k k'
      let a : P'.homology p ⟶ P.homology p := homologyMap f p
      let c : Y p ⟶ Y' p := b p
      apply ULift.ext
      change a ≫ (k.down + k'.down) ≫ c = a ≫ k.down ≫ c + a ≫ k'.down ≫ c
      calc
        _ = (a ≫ (k.down + k'.down)) ≫ c := (Category.assoc _ _ _).symm
        _ = (a ≫ k.down + a ≫ k'.down) ≫ c :=
          congrArg (fun t => t ≫ c)
            (Preadditive.comp_add (P'.homology p) (P.homology p) (Y p) a k.down k'.down)
        _ = (a ≫ k.down) ≫ c + (a ≫ k'.down) ≫ c :=
          Preadditive.add_comp (P'.homology p) (Y p) (Y' p) (a ≫ k.down) (a ≫ k'.down) c
        _ = _ := congrArg₂ (fun t t' => t + t')
          (Category.assoc a k.down c) (Category.assoc a k'.down c))
  exact AddCommGrpCat.ofHom (AddMonoidHom.piMap m)

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. The πₚ-precomposition inclusions into cycle Hom commute with
the product map tₚ ↦ bₚ ∘ tₚ ∘ Hₚ(f) and the corresponding cycle-Hom presentation map. -/
lemma homUctHomKernelInclusion_naturality {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    homUctHomKernelInclusion P Y ≫ (homUctProductPresentationMap f b).τ₁ =
      homUctHomProductMap f b ≫ homUctHomKernelInclusion P' Y' := by
  let A : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p))
  let A' : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P'.homology p ⟶ Y' p))
  let S : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let T : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P' Y'
  let κ : A ⟶ S.X₁ := homUctHomKernelInclusion P Y
  let κ' : A' ⟶ T.X₁ := homUctHomKernelInclusion P' Y'
  let a : S.X₁ ⟶ T.X₁ := (homUctProductPresentationMap f b).τ₁
  let m : A ⟶ A' := homUctHomProductMap f b
  apply AddCommGrpCat.ext
  intro k
  funext p
  let v : P.homology p ⟶ Y p := (k p).down
  let c : P'.cycles p ⟶ P.cycles p := cyclesMap f p
  let h : P'.homology p ⟶ P.homology p := homologyMap f p
  let π : P.cycles p ⟶ P.homology p := P.homologyπ p
  let π' : P'.cycles p ⟶ P'.homology p := P'.homologyπ p
  let t : Y p ⟶ Y' p := b p
  have hLeft : (κ ≫ a).hom k p = ULift.up (c ≫ (π ≫ v) ≫ t) :=
    (congrArg (fun z : T.X₁ => z p) (AddCommGrpCat.comp_apply κ a k)).trans
      (homUctProductPresentationMap_τ₁_apply f b (κ.hom k) p)
  have hRight : (m ≫ κ').hom k p = ULift.up (π' ≫ (h ≫ v ≫ t)) :=
    congrArg (fun z : T.X₁ => z p) (AddCommGrpCat.comp_apply m κ' k)
  have hπ : π' ≫ h = c ≫ π := homologyπ_naturality f p
  have hValue : c ≫ (π ≫ v) ≫ t = π' ≫ (h ≫ v ≫ t) := by
    calc
      _ = (c ≫ π) ≫ v ≫ t := by simp only [Category.assoc]
      _ = (π' ≫ h) ≫ v ≫ t := congrArg (fun a => a ≫ v ≫ t) hπ.symm
      _ = π' ≫ (h ≫ v ≫ t) := by simp only [Category.assoc]
  change (κ ≫ a).hom k p = (m ≫ κ').hom k p
  exact hLeft.trans ((congrArg (fun z : P'.cycles p ⟶ Y' p =>
    (ULift.up z : ULift.{w, v} (P'.cycles p ⟶ Y' p))) hValue).trans hRight.symm)

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. The actual square of β-precomposition maps induces the map
between the full-presentation kernels for (P,Y) and (P′,Y′). -/
def homUctHomKernelMap {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    kernel (homUctProductPresentation P Y).f ⟶
      kernel (homUctProductPresentation P' Y').f :=
  kernel.map _ _ (homUctProductPresentationMap f b).τ₁
    (homUctProductPresentationMap f b).τ₂ (homUctProductPresentationMap f b).comm₁₂.symm

/-- Let C be an abelian category with object universe u and morphism universe v. Assume Ext_C is
available in an independent universe w. Let f : P′ → P be an integer chain map, Y,Y′ : ℤ → C
coefficient families, and bₚ : Yₚ → Y′ₚ. Write Bₚ,Zₚ,Hₚ for the boundary, cycles and homology
objects of P, and similarly for P′. The kernel-to-product-Hom comparisons commute with the
induced kernel map and coordinatewise precomposition by Hₚ(f) and postcomposition by bₚ. -/
lemma homUctHomKernelIso_naturality {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    {Y Y' : ℤ → C} (b : ∀ p, Y p ⟶ Y' p) :
    homUctHomKernelMap f b ≫ (homUctHomKernelIso P' Y').hom =
      (homUctHomKernelIso P Y).hom ≫ homUctHomProductMap f b := by
  let S : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P Y
  let T : ShortComplex AddCommGrpCat.{max v w} := homUctProductPresentation P' Y'
  let A : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Y p))
  let B : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P'.homology p ⟶ Y' p))
  let e : kernel S.f ≅ A := homUctHomKernelIso P Y
  let e' : kernel T.f ≅ B := homUctHomKernelIso P' Y'
  let κ : A ⟶ S.X₁ := homUctHomKernelInclusion P Y
  let κ' : B ⟶ T.X₁ := homUctHomKernelInclusion P' Y'
  let ι : kernel S.f ⟶ S.X₁ := kernel.ι S.f
  let ι' : kernel T.f ⟶ T.X₁ := kernel.ι T.f
  let φ : S ⟶ T := homUctProductPresentationMap f b
  let m : kernel S.f ⟶ kernel T.f := homUctHomKernelMap f b
  let h : A ⟶ B := homUctHomProductMap f b
  letI : Mono κ' := homUctHomKernelInclusion_mono P' Y'
  have hm : m ≫ ι' = ι ≫ φ.τ₁ := by
    dsimp only [m, homUctHomKernelMap, kernel.map]
    exact kernel.lift_ι _ _ _
  have he : e.hom ≫ κ = ι := homUctHomKernelIso_hom_inclusion P Y
  have he' : e'.hom ≫ κ' = ι' := homUctHomKernelIso_hom_inclusion P' Y'
  have hκ : κ ≫ φ.τ₁ = h ≫ κ' := homUctHomKernelInclusion_naturality f b
  apply (cancel_mono κ').1
  change (m ≫ e'.hom) ≫ κ' = (e.hom ≫ h) ≫ κ'
  calc
    _ = m ≫ (e'.hom ≫ κ') := Category.assoc _ _ _
    _ = m ≫ ι' := congrArg (fun a => m ≫ a) he'
    _ = ι ≫ φ.τ₁ := hm
    _ = (e.hom ≫ κ) ≫ φ.τ₁ := congrArg (fun a => a ≫ φ.τ₁) he.symm
    _ = e.hom ≫ (κ ≫ φ.τ₁) := Category.assoc _ _ _
    _ = e.hom ≫ (h ≫ κ') := congrArg (fun a => e.hom ≫ a) hκ
    _ = (e.hom ≫ h) ≫ κ' := (Category.assoc _ _ _).symm

end ExtPresentation

section LiftedCohomology

open ComposableArrows

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
The four-arrow exact window is H^{n-1} Hom(Z⁰,Q) → Hⁿ Hom(I⁰,Q) → Hⁿ Hom(P,Q) → Hⁿ Hom(Z⁰,Q) →
H^{n+1} Hom(I⁰,Q), with outside arrows δₙ₋₁ and δₙ and inside arrows induced by the Hom
inclusion and restriction. -/
def homCyclesFourArrowSequence (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ComposableArrows AddCommGrpCat.{max v w} 4 :=
  let S := homCyclesSequence P Q
  let hS := homCyclesSequence_shortExact P Q hI
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  mk₄ (U.map (hS.δ (n - 1) n (ComplexShape.up_mk (n - 1) n (by omega))))
    (U.map (HomologicalComplex.homologyMap S.f n))
    (U.map (HomologicalComplex.homologyMap S.g n))
    (U.map (hS.δ n (n + 1) rfl))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
The four arrows surrounding Hⁿ Hom(P,Q) form an exact window, after canonical common-universe
transport. Only projectivity of the differential images is required. -/
lemma homCyclesFourArrowSequence_exact (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCyclesFourArrowSequence.{u, v, w} P Q n hI).Exact := by
  let hS := homCyclesSequence_shortExact P Q hI
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  exact exact_of_δ₀
    ((hS.homology_exact₁ (n - 1) n
      (ComplexShape.up_mk (n - 1) n (by omega))).map U).exact_toComposableArrows
    (exact_of_δ₀ ((hS.homology_exact₂ n).map U).exact_toComposableArrows
      ((hS.homology_exact₃ n (n + 1) rfl).map U).exact_toComposableArrows)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
The window gives the natural short complex coker(δₙ₋₁) → Hⁿ Hom(P,Q) → ker(δₙ). Its arrows are
the canonical maps induced by exactness of the Hom cohomology sequence. -/
def homCyclesCohomologyClip (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ShortComplex AddCommGrpCat.{max v w} :=
  middleKernelCokernelSequence (homCyclesFourArrowSequence P Q n hI)
    (homCyclesFourArrowSequence_exact P Q n hI).toIsComplex

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
The induced sequence 0 → coker(δₙ₋₁) → Hⁿ Hom(P,Q) → ker(δₙ) → 0 is short exact. No projectivity
of the terms Pₚ is used for this clipped sequence. -/
lemma homCyclesCohomologyClip_shortExact (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCyclesCohomologyClip.{u, v, w} P Q n hI).ShortExact :=
  middleKernelCokernelSequence_shortExact _ (homCyclesFourArrowSequence_exact P Q n hI)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
The middle object of coker(δₙ₋₁) → Hⁿ Hom(P,Q) → ker(δₙ) is exactly the cohomology of the full
Hom cochain product, in the common group universe. Neither differential of P or Q is replaced. -/
lemma homCyclesCohomologyClip_X₂ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCyclesCohomologyClip.{u, v, w} P Q n hI).X₂ =
      AddCommGrpCat.uliftFunctor.{w, v}.obj ((homCochainComplex P Q).homology n) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let f : P′ → P and
g : Q → Q′ be integer chain and cochain maps, respectively, and let n ∈ ℤ. Assume all
differential images of P and P′ are projective. The induced map of short exact Hom sequences
gives a map of their four-arrow cohomology windows, including both connecting arrows. The map is
contravariant in P and covariant in Q. -/
def homCyclesFourArrowSequenceMap {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    homCyclesFourArrowSequence.{u, v, w} P Q n hI ⟶
      homCyclesFourArrowSequence P' Q' n hI' := by
  let S := homCyclesSequence P Q
  let T := homCyclesSequence P' Q'
  let hS := homCyclesSequence_shortExact P Q hI
  let hT := homCyclesSequence_shortExact P' Q' hI'
  let φ : S ⟶ T := homCyclesSequenceMap f g
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let hRel : (ComplexShape.up ℤ).Rel (n - 1) n :=
    ComplexShape.up_mk (n - 1) n (by omega)
  refine homMk₄ (U.map (HomologicalComplex.homologyMap φ.τ₃ (n - 1)))
    (U.map (HomologicalComplex.homologyMap φ.τ₁ n))
    (U.map (HomologicalComplex.homologyMap φ.τ₂ n))
    (U.map (HomologicalComplex.homologyMap φ.τ₃ n))
    (U.map (HomologicalComplex.homologyMap φ.τ₁ (n + 1))) ?_ ?_ ?_ ?_
  · change U.map (hS.δ (n - 1) n hRel) ≫
        U.map (HomologicalComplex.homologyMap φ.τ₁ n) =
      U.map (HomologicalComplex.homologyMap φ.τ₃ (n - 1)) ≫
        U.map (hT.δ (n - 1) n hRel)
    simpa only [U.map_comp] using congrArg U.map
      (HomologicalComplex.HomologySequence.δ_naturality φ hS hT (n - 1) n hRel)
  · change U.map (HomologicalComplex.homologyMap S.f n) ≫
        U.map (HomologicalComplex.homologyMap φ.τ₂ n) =
      U.map (HomologicalComplex.homologyMap φ.τ₁ n) ≫
        U.map (HomologicalComplex.homologyMap T.f n)
    simpa only [HomologicalComplex.homologyMap_comp, U.map_comp] using
      congrArg (fun k : S.X₁ ⟶ T.X₂ => U.map (HomologicalComplex.homologyMap k n))
        φ.comm₁₂.symm
  · change U.map (HomologicalComplex.homologyMap S.g n) ≫
        U.map (HomologicalComplex.homologyMap φ.τ₃ n) =
      U.map (HomologicalComplex.homologyMap φ.τ₂ n) ≫
        U.map (HomologicalComplex.homologyMap T.g n)
    simpa only [HomologicalComplex.homologyMap_comp, U.map_comp] using
      congrArg (fun k : S.X₂ ⟶ T.X₃ => U.map (HomologicalComplex.homologyMap k n))
        φ.comm₂₃.symm
  · change U.map (hS.δ n (n + 1) rfl) ≫
        U.map (HomologicalComplex.homologyMap φ.τ₁ (n + 1)) =
      U.map (HomologicalComplex.homologyMap φ.τ₃ n) ≫ U.map (hT.δ n (n + 1) rfl)
    simpa only [U.map_comp] using congrArg U.map
      (HomologicalComplex.HomologySequence.δ_naturality φ hS hT n (n + 1) rfl)

/-- Let C be an abelian category with object universe u and morphism universe v. Let f : P′ → P and
g : Q → Q′ be integer chain and cochain maps, respectively, and let n ∈ ℤ. Assume all
differential images of P and P′ are projective. The actual window map induces a map coker(δₙ₋₁)
→ Hⁿ Hom(P,Q) → ker(δₙ) to the corresponding clipped sequence for (P′,Q′), using the induced
cokernel and kernel maps. -/
def homCyclesCohomologyClipMap {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    homCyclesCohomologyClip.{u, v, w} P Q n hI ⟶ homCyclesCohomologyClip P' Q' n hI' :=
  middleKernelCokernelSequenceMap (homCyclesFourArrowSequenceMap f g n hI hI')
    (homCyclesFourArrowSequence_exact P Q n hI).toIsComplex
    (homCyclesFourArrowSequence_exact P' Q' n hI').toIsComplex

/-- Let C be an abelian category with object universe u and morphism universe v. Let f : P′ → P and
g : Q → Q′ be integer chain and cochain maps, respectively, and let n ∈ ℤ. Assume all
differential images of P and P′ are projective. The middle component of the clipped-sequence map
is Hⁿ Hom(f,g), with its canonical common-universe transport. -/
lemma homCyclesCohomologyClipMap_τ₂ {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homCyclesCohomologyClipMap.{u, v, w} f g n hI hI').τ₂ =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCochainComplexMap f g) n) := rfl

end LiftedCohomology

section Endpoints

variable [HasExt.{w} C]

private lemma nextDownInt (p : ℤ) : (ComplexShape.down ℤ).next p = p - 1 :=
  (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume every cycle object Zₚ(P) is
projective. The full cohomology comparison is Hⁿ Hom(Z⁰(P),Q) ≅ ∏ₚ Hom_C(Zₚ(P),H^{n-p}(Q)), in
the common group universe max(v,w). -/
def homUctCyclesCohomologyIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    AddCommGrpCat.uliftFunctor.{w, v}.obj
        ((homCochainComplex (cyclesZeroComplex P) Q).homology n) ≅
      (homUctProductPresentation P (fun p => Q.homology (n - p))).X₁ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let H := homCochainComplex (cyclesZeroComplex P) Q
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let A (p : ℤ) : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (P.cycles p ⟶ Q.homology (n - p))
  let T : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.cycles p ⟶ Q.homology (n - p)))
  let hCycles (p : ℤ) : Projective ((cyclesZeroComplex P).X p) := by
    change Projective (P.cycles p)
    exact hZ p
  let e : H.homology n ≅ G :=
    homZeroSourceCohomologyIso (cyclesZeroComplex P) Q n (by intro i j; rfl) hCycles
  let t : U.obj G ≅ T := AddCommGrpCat.uliftIntPiIso A
  change U.obj (H.homology n) ≅ T
  exact U.mapIso e ≪≫ t

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. For integers n,m with m=n+1,
reindexing outgoing images in source degree p+1 identifies ∏ᵢ Hom_C(im d_P^{i,i-1},H^{m-i}(Q))
with ∏ₚ Hom_C(Bₚ(P),H^{n-p}(Q)), using the actual adjacent-degree identifications. -/
def homUctImageProductIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n m : ℤ)
    (hnm : n + 1 = m) :
    AddCommGrpCat.uliftFunctor.{w, v}.obj
        (AddCommGrpCat.of (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶
          Q.homology (m - p))) ≅
      (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let A (p : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    ((outgoingImageZeroComplex P).X p ⟶ Q.homology (m - p))
  let B (p : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    ((homUctBoundaryPresentation P p).X₁ ⟶ Q.homology (n - p))
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of (∀ p : ℤ, A p)
  let T₁ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, U.obj (A p))
  let T₂ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, U.obj (B p))
  let reindex : (∀ p : ℤ, U.obj (A p)) ≃+ (∀ p : ℤ, U.obj (A (p + 1))) :=
    { toEquiv := (Equiv.piCongrLeft (fun p : ℤ => U.obj (A p)) (Equiv.addRight 1)).symm
      map_add' _ _ := rfl }
  let eI (p : ℤ) : (homUctBoundaryPresentation P p).X₁ ≅
      (outgoingImageZeroComplex P).X (p + 1) := eqToIso (by
    change Abelian.image (P.d (p + 1) p) =
      Abelian.image (P.d (p + 1) ((ComplexShape.down ℤ).next (p + 1)))
    exact congrArg (fun i => Abelian.image (P.d (p + 1) i))
      ((ComplexShape.down ℤ).next_eq'
        (ComplexShape.down_mk (p + 1) p (by omega))).symm)
  let eQ (p : ℤ) : Q.homology (m - (p + 1)) ≅ Q.homology (n - p) :=
    eqToIso (congrArg (fun k : ℤ => (Q.homology k : C)) (by omega))
  let e (p : ℤ) : A (p + 1) ≅ B p :=
    (preadditiveYoneda.obj (Q.homology (m - (p + 1)))).mapIso (eI p).op ≪≫
      (preadditiveCoyoneda.obj (op (homUctBoundaryPresentation P p).X₁)).mapIso (eQ p)
  let q : T₁ ≅ T₂ :=
    (reindex.trans (AddEquiv.piCongrRight fun p =>
      (U.mapIso (e p)).addCommGroupIsoToAddEquiv)).toAddCommGrpIso
  let t : U.obj G ≅ T₁ := AddCommGrpCat.uliftIntPiIso A
  change U.obj G ≅ T₂
  exact t ≪≫ q

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. For m=n+1, the p-th reindexed
component is the original morphism in source degree p+1, precomposed with the canonical image
identification Bₚ ≅ im d_P^{p+1,p} and followed by the equality H^{m-(p+1)}(Q)=H^{n-p}(Q). -/
lemma homUctImageProductIso_hom_up (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m)
    (k : ∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (m - p)) (p : ℤ) :
    let eI : (homUctBoundaryPresentation P p).X₁ ≅
        (outgoingImageZeroComplex P).X (p + 1) := eqToIso (by
      change Abelian.image (P.d (p + 1) p) =
        Abelian.image (P.d (p + 1) ((ComplexShape.down ℤ).next (p + 1)))
      exact congrArg (fun i => Abelian.image (P.d (p + 1) i))
        ((ComplexShape.down ℤ).next_eq'
          (ComplexShape.down_mk (p + 1) p (by omega))).symm)
    (homUctImageProductIso P Q n m hnm).hom (ULift.up k) p =
      ULift.up (eI.hom ≫ k (p + 1) ≫
        eqToHom (congrArg (fun k : ℤ => (Q.homology k : C))
          (by omega : m - (p + 1) = n - p))) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let A (r : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    ((outgoingImageZeroComplex P).X r ⟶ Q.homology (m - r))
  let B (r : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of
    ((homUctBoundaryPresentation P r).X₁ ⟶ Q.homology (n - r))
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of (∀ r : ℤ, A r)
  let T₁ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ r : ℤ, U.obj (A r))
  let T₂ : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ r : ℤ, U.obj (B r))
  let eI (r : ℤ) : (homUctBoundaryPresentation P r).X₁ ≅
      (outgoingImageZeroComplex P).X (r + 1) := eqToIso (by
    change Abelian.image (P.d (r + 1) r) =
      Abelian.image (P.d (r + 1) ((ComplexShape.down ℤ).next (r + 1)))
    exact congrArg (fun i => Abelian.image (P.d (r + 1) i))
      ((ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (r + 1) r (by omega))).symm)
  let eQ (r : ℤ) : Q.homology (m - (r + 1)) ≅ Q.homology (n - r) :=
    eqToIso (congrArg (fun i : ℤ => (Q.homology i : C)) (by omega))
  let e (r : ℤ) : A (r + 1) ≅ B r :=
    (preadditiveYoneda.obj (Q.homology (m - (r + 1)))).mapIso (eI r).op ≪≫
      (preadditiveCoyoneda.obj (op (homUctBoundaryPresentation P r).X₁)).mapIso (eQ r)
  let reindex : (∀ r : ℤ, U.obj (A r)) ≃+ (∀ r : ℤ, U.obj (A (r + 1))) :=
    { toEquiv := (Equiv.piCongrLeft (fun r : ℤ => U.obj (A r)) (Equiv.addRight 1)).symm
      map_add' _ _ := rfl }
  let q : T₁ ≅ T₂ :=
    (reindex.trans (AddEquiv.piCongrRight fun r =>
      (U.mapIso (e r)).addCommGroupIsoToAddEquiv)).toAddCommGrpIso
  let t : U.obj G ≅ T₁ := AddCommGrpCat.uliftIntPiIso A
  let E : U.obj G ≅ T₂ := homUctImageProductIso P Q n m hnm
  let k₀ : G := k
  let z : T₁ := t.hom.hom (ULift.up k₀)
  have hz : z (p + 1) = ULift.up (k (p + 1)) :=
    AddCommGrpCat.uliftIntPiIso_hom_up A k₀ (p + 1)
  have hq : q.hom.hom z p = (U.map (e p).hom).hom (z (p + 1)) := rfl
  let M : AddCommGrpCat.{v} := AddCommGrpCat.of
    ((homUctBoundaryPresentation P p).X₁ ⟶ Q.homology (m - (p + 1)))
  let a : A (p + 1) ≅ M :=
    (preadditiveYoneda.obj (Q.homology (m - (p + 1)))).mapIso (eI p).op
  let b : M ≅ B p :=
    (preadditiveCoyoneda.obj (op (homUctBoundaryPresentation P p).X₁)).mapIso (eQ p)
  have he : (e p).hom = a.hom ≫ b.hom := rfl
  have ha : a.hom.hom (k (p + 1)) = (eI p).hom ≫ k (p + 1) := rfl
  have hb : b.hom.hom ((eI p).hom ≫ k (p + 1)) =
      ((eI p).hom ≫ k (p + 1)) ≫ (eQ p).hom := rfl
  have hNative : (e p).hom.hom (k (p + 1)) =
      (eI p).hom ≫ k (p + 1) ≫ (eQ p).hom :=
    (ConcreteCategory.congr_hom he (k (p + 1))).trans
      ((AddCommGrpCat.comp_apply a.hom b.hom (k (p + 1))).trans
        ((congrArg b.hom.hom ha).trans
          (hb.trans (Category.assoc (eI p).hom (k (p + 1)) (eQ p).hom))))
  have hu : (U.map (e p).hom).hom (ULift.up (k (p + 1))) =
      ULift.up ((e p).hom.hom (k (p + 1))) := rfl
  have hValue : E.hom.hom (ULift.up k₀) = q.hom.hom z := rfl
  change E.hom.hom (ULift.up k₀) p =
    ULift.up ((eI p).hom ≫ k (p + 1) ≫ (eQ p).hom)
  exact (congrFun hValue p).trans
    (hq.trans ((congrArg (U.map (e p).hom).hom hz).trans
      (hu.trans (congrArg ULift.up hNative))))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. For m=n+1, projectivity of the images identifies Hᵐ
Hom(I⁰(P),Q) with the full product ∏ₚ Hom_C(Bₚ(P),H^{n-p}(Q)), after reindexing the actual
source image degree p+1. -/
def homUctImagesCohomologyIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n m : ℤ)
    (hnm : n + 1 = m) (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    AddCommGrpCat.uliftFunctor.{w, v}.obj
        ((homCochainComplex (outgoingImageZeroComplex P) Q).homology m) ≅
      (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let H := homCochainComplex (outgoingImageZeroComplex P) Q
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (m - p))
  let T : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂
  let hOut (p : ℤ) : Projective ((outgoingImageZeroComplex P).X p) := by
    change Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))
    rw [nextDownInt p]
    exact hI p
  let e : H.homology m ≅ G :=
    homZeroSourceCohomologyIso (outgoingImageZeroComplex P) Q m
      (by intro i j; rfl) hOut
  let t : U.obj G ≅ T := homUctImageProductIso P Q n m hnm
  exact U.mapIso e ≪≫ t

/-- Let C be an abelian category with object universe u and morphism universe v. Let f : P′ → P and
g : Q → Q′ be integer chain and cochain maps, respectively, and let n ∈ ℤ. If every cycle of P
and P′ is projective, the comparisons Hⁿ Hom(Z⁰(P),Q) ≅ ∏ₚ Hom(Zₚ(P),H^{n-p}(Q)) commute with
Hom cohomology of the cycle map and with coordinatewise cycle precomposition and target homology
postcomposition. -/
lemma homUctCyclesCohomologyIso_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hZ : ∀ p : ℤ, Projective (P.cycles p))
    (hZ' : ∀ p : ℤ, Projective (P'.cycles p)) :
    AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₃ n) ≫
        (homUctCyclesCohomologyIso P' Q' n hZ').hom =
      (homUctCyclesCohomologyIso P Q n hZ).hom ≫
        (homUctProductPresentationMap f
          (fun p => HomologicalComplex.homologyMap g (n - p))).τ₁ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let Z := homCochainComplex (cyclesZeroComplex P) Q
  let Z' := homCochainComplex (cyclesZeroComplex P') Q'
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let G' : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P'.cycles p ⟶ Q'.homology (n - p))
  let A (p : ℤ) : AddCommGrpCat.{v} := AddCommGrpCat.of (P.cycles p ⟶ Q.homology (n - p))
  let A' (p : ℤ) : AddCommGrpCat.{v} :=
    AddCommGrpCat.of (P'.cycles p ⟶ Q'.homology (n - p))
  let T : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, U.obj (A p))
  let T' : AddCommGrpCat.{max v w} := AddCommGrpCat.of (∀ p : ℤ, U.obj (A' p))
  let fZ : cyclesZeroComplex P' ⟶ cyclesZeroComplex P :=
    ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₁
  let hCycles (p : ℤ) : Projective ((cyclesZeroComplex P).X p) := by
    change Projective (P.cycles p)
    exact hZ p
  let hCycles' (p : ℤ) : Projective ((cyclesZeroComplex P').X p) := by
    change Projective (P'.cycles p)
    exact hZ' p
  let c : Z.homology n ≅ G :=
    homZeroSourceCohomologyIso (cyclesZeroComplex P) Q n (by intro i j; rfl) hCycles
  let c' : Z'.homology n ≅ G' :=
    homZeroSourceCohomologyIso (cyclesZeroComplex P') Q' n (by intro i j; rfl) hCycles'
  let t : U.obj G ≅ T := AddCommGrpCat.uliftIntPiIso A
  let t' : U.obj G' ≅ T' := AddCommGrpCat.uliftIntPiIso A'
  let e : U.obj (Z.homology n) ≅ T := homUctCyclesCohomologyIso P Q n hZ
  let e' : U.obj (Z'.homology n) ≅ T' := homUctCyclesCohomologyIso P' Q' n hZ'
  let b : G ⟶ G' := homCohomologyProductMap fZ g n
  let τ : T ⟶ T' := (homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - p))).τ₁
  let m : U.obj (Z.homology n) ⟶ U.obj (Z'.homology n) :=
    U.map (HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₃ n)
  let m₀ : U.obj (Z.homology n) ⟶ U.obj (Z'.homology n) :=
    U.map (HomologicalComplex.homologyMap (homCochainComplexMap fZ g) n)
  have hm : m = m₀ := congrArg (fun k => U.map (HomologicalComplex.homologyMap k n))
    (homCyclesSequenceMap_τ₃ f g)
  have he : e.hom = U.map c.hom ≫ t.hom := rfl
  have he' : e'.hom = U.map c'.hom ≫ t'.hom := rfl
  have hLift : U.map b ≫ t'.hom = t.hom ≫ τ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro k
    cases k with
    | up k =>
      let k₀ : G := k
      let z : T := t.hom.hom (ULift.up k₀)
      have hz (p : ℤ) : z p = ULift.up (k₀ p) := AddCommGrpCat.uliftIntPiIso_hom_up A k₀ p
      have hu : (U.map b).hom (ULift.up k₀) = ULift.up (b.hom k₀) := rfl
      have hLeft : (U.map b ≫ t'.hom).hom (ULift.up k₀) =
          t'.hom.hom (ULift.up (b.hom k₀)) :=
        (AddCommGrpCat.comp_apply (U.map b) t'.hom (ULift.up k₀)).trans
          (congrArg t'.hom.hom hu)
      have hRight : (t.hom ≫ τ).hom (ULift.up k₀) = τ.hom z :=
        AddCommGrpCat.comp_apply t.hom τ (ULift.up k₀)
      have hPoint : t'.hom.hom (ULift.up (b.hom k₀)) = τ.hom z := by
        funext p
        have hf : fZ.f p = HomologicalComplex.cyclesMap f p := rfl
        have hb₀ : b.hom k₀ p =
            fZ.f p ≫ k₀ p ≫ HomologicalComplex.homologyMap g (n - p) := rfl
        have hb : b.hom k₀ p =
            HomologicalComplex.cyclesMap f p ≫ k₀ p ≫ HomologicalComplex.homologyMap g (n - p) :=
          hb₀.trans
            (congrArg (fun h => h ≫ k₀ p ≫ HomologicalComplex.homologyMap g (n - p)) hf)
        have hτ := homUctProductPresentationMap_τ₁_apply f
          (fun p => HomologicalComplex.homologyMap g (n - p)) z p
        exact (AddCommGrpCat.uliftIntPiIso_hom_up A' (b.hom k₀) p).trans
          ((congrArg ULift.up hb).trans
            ((congrArg (fun h => ULift.up (HomologicalComplex.cyclesMap f p ≫ h.down ≫
              HomologicalComplex.homologyMap g (n - p))) (hz p)).symm.trans hτ.symm))
      exact hLeft.trans (hPoint.trans hRight.symm)
  have hNative : m₀ ≫ U.map c'.hom = U.map c.hom ≫ U.map b :=
    (U.map_comp _ _).symm.trans
      ((congrArg (fun h => U.map h)
        (homZeroSourceCohomologyIso_naturality fZ g n
          (by intro i j; rfl) (by intro i j; rfl) hCycles hCycles')).trans (U.map_comp _ _))
  change m ≫ e'.hom = e.hom ≫ τ
  calc
    _ = m₀ ≫ (U.map c'.hom ≫ t'.hom) := congrArg₂ (fun a b => a ≫ b) hm he'
    _ = (U.map c.hom ≫ U.map b) ≫ t'.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ t'.hom) hNative)
    _ = U.map c.hom ≫ (t.hom ≫ τ) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => U.map c.hom ≫ a) hLift)
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ τ) he.symm)

omit [HasExt.{w} C] in
private lemma imageMap_target_eq {P P' : ChainComplex C ℤ} (f : P' ⟶ P)
    (p i j : ℤ) (h : i = j) :
    let aᵢ : Arrow.mk (P'.d p i) ⟶ Arrow.mk (P.d p i) :=
      Arrow.homMk (f.f p) (f.f i) (f.comm p i)
    let aⱼ : Arrow.mk (P'.d p j) ⟶ Arrow.mk (P.d p j) :=
      Arrow.homMk (f.f p) (f.f j) (f.comm p j)
    let mᵢ : Abelian.image (P'.d p i) ⟶ Abelian.image (P.d p i) := by
      let m₀ := (Abelian.im (C := C)).map aᵢ
      dsimp only [Abelian.im_obj, Arrow.mk] at m₀
      exact m₀
    let mⱼ : Abelian.image (P'.d p j) ⟶ Abelian.image (P.d p j) := by
      let m₀ := (Abelian.im (C := C)).map aⱼ
      dsimp only [Abelian.im_obj, Arrow.mk] at m₀
      exact m₀
    eqToHom (congrArg (fun r => Abelian.image (P'.d p r)) h.symm) ≫ mᵢ =
      mⱼ ≫ eqToHom (congrArg (fun r => Abelian.image (P.d p r)) h.symm) := by
  subst j
  let a : Arrow.mk (P'.d p i) ⟶ Arrow.mk (P.d p i) :=
    Arrow.homMk (f.f p) (f.f i) (f.comm p i)
  let m₀ := (Abelian.im (C := C)).map a
  let m : Abelian.image (P'.d p i) ⟶ Abelian.image (P.d p i) := by
    dsimp only [Abelian.im_obj, Arrow.mk] at m₀
    exact m₀
  change (𝟙 (Abelian.image (P'.d p i))) ≫ m = m ≫ 𝟙 (Abelian.image (P.d p i))
  exact (Category.id_comp m).trans (Category.comp_id m).symm

omit [HasExt.{w} C] in
private lemma homologyMap_degree_eq {Q Q' : CochainComplex C ℤ} (g : Q ⟶ Q')
    {i j : ℤ} (h : i = j) :
    HomologicalComplex.homologyMap g i ≫ eqToHom (congrArg (fun k : ℤ => (Q'.homology k : C)) h) =
      eqToHom (congrArg (fun k : ℤ => (Q.homology k : C)) h) ≫
        HomologicalComplex.homologyMap g j := by
  subst j
  let m : Q.homology i ⟶ Q'.homology i := HomologicalComplex.homologyMap g i
  simp only [eqToHom_refl]
  change m ≫ 𝟙 (Q'.homology i) = 𝟙 (Q.homology i) ≫ m
  exact (Category.comp_id m).trans (Category.id_comp m).symm

private lemma imageProduct_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q')
    (n m : ℤ) (hnm : n + 1 = m) :
    let fI : outgoingImageZeroComplex P' ⟶ outgoingImageZeroComplex P :=
      ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₃
    AddCommGrpCat.uliftFunctor.{w, v}.map (homCohomologyProductMap fI g m) ≫
        (homUctImageProductIso P' Q' n m hnm).hom =
      (homUctImageProductIso P Q n m hnm).hom ≫
        (homUctProductPresentationMap f
          (fun p => HomologicalComplex.homologyMap g (n - p))).τ₂ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (m - p))
  let G' : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P').X p ⟶ Q'.homology (m - p))
  let T : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂
  let T' : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P' (fun p => Q'.homology (n - p))).X₂
  let fI : outgoingImageZeroComplex P' ⟶ outgoingImageZeroComplex P :=
    ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₃
  let b : G ⟶ G' := homCohomologyProductMap fI g m
  let E : U.obj G ≅ T := homUctImageProductIso P Q n m hnm
  let E' : U.obj G' ≅ T' := homUctImageProductIso P' Q' n m hnm
  let τ : T ⟶ T' := (homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - p))).τ₂
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro k
  cases k with
  | up k =>
    let k₀ : G := k
    let z : T := E.hom.hom (ULift.up k₀)
    have hu : (U.map b).hom (ULift.up k₀) = ULift.up (b.hom k₀) := rfl
    have hLeft : (U.map b ≫ E'.hom).hom (ULift.up k₀) =
        E'.hom.hom (ULift.up (b.hom k₀)) :=
      (AddCommGrpCat.comp_apply (U.map b) E'.hom (ULift.up k₀)).trans
        (congrArg E'.hom.hom hu)
    have hRight : (E.hom ≫ τ).hom (ULift.up k₀) = τ.hom z :=
      AddCommGrpCat.comp_apply E.hom τ (ULift.up k₀)
    have hValue : E'.hom.hom (ULift.up (b.hom k₀)) = τ.hom z := by
      funext p
      have hNext : (ComplexShape.down ℤ).next (p + 1) = p :=
        (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (p + 1) p (by omega))
      let eI : (homUctBoundaryPresentation P p).X₁ ≅
          (outgoingImageZeroComplex P).X (p + 1) :=
        eqToIso (congrArg (fun i => Abelian.image (P.d (p + 1) i)) hNext.symm)
      let eI' : (homUctBoundaryPresentation P' p).X₁ ≅
          (outgoingImageZeroComplex P').X (p + 1) :=
        eqToIso (congrArg (fun i => Abelian.image (P'.d (p + 1) i)) hNext.symm)
      let eQ : Q.homology (m - (p + 1)) ≅ Q.homology (n - p) :=
        eqToIso (congrArg (fun i : ℤ => (Q.homology i : C)) (by omega))
      let eQ' : Q'.homology (m - (p + 1)) ≅ Q'.homology (n - p) :=
        eqToIso (congrArg (fun i : ℤ => (Q'.homology i : C)) (by omega))
      let a : (homUctBoundaryPresentation P' p).X₁ ⟶
          (homUctBoundaryPresentation P p).X₁ := (homUctBoundaryPresentationMap f p).τ₁
      let h : Q.homology (m - (p + 1)) ⟶ Q'.homology (m - (p + 1)) :=
        HomologicalComplex.homologyMap g (m - (p + 1))
      let h' : Q.homology (n - p) ⟶ Q'.homology (n - p) :=
        HomologicalComplex.homologyMap g (n - p)
      have hI : eI'.hom ≫ fI.f (p + 1) = a ≫ eI.hom :=
        imageMap_target_eq f (p + 1) _ p hNext
      have hQ : h ≫ eQ'.hom = eQ.hom ≫ h' := homologyMap_degree_eq g (by omega)
      have hMap : b.hom k₀ (p + 1) = fI.f (p + 1) ≫ k₀ (p + 1) ≫ h :=
        rfl
      have hE : E'.hom.hom (ULift.up (b.hom k₀)) p =
          ULift.up (eI'.hom ≫ b.hom k₀ (p + 1) ≫ eQ'.hom) :=
        homUctImageProductIso_hom_up P' Q' n m hnm (b.hom k₀) p
      have hz : z p = ULift.up (eI.hom ≫ k₀ (p + 1) ≫ eQ.hom) :=
        homUctImageProductIso_hom_up P Q n m hnm k₀ p
      have hτ : τ.hom z p = ULift.up (a ≫ (z p).down ≫ h') :=
        homUctProductPresentationMap_τ₂_apply f
          (fun p => HomologicalComplex.homologyMap g (n - p)) z p
      have hComp : eI'.hom ≫ b.hom k₀ (p + 1) ≫ eQ'.hom =
          a ≫ (eI.hom ≫ k₀ (p + 1) ≫ eQ.hom) ≫ h' := by
        calc
          _ = eI'.hom ≫ (fI.f (p + 1) ≫ k₀ (p + 1) ≫ h) ≫ eQ'.hom :=
            congrArg (fun v => eI'.hom ≫ v ≫ eQ'.hom) hMap
          _ = (eI'.hom ≫ fI.f (p + 1)) ≫ k₀ (p + 1) ≫ (h ≫ eQ'.hom) := by
            simp only [Category.assoc]
          _ = (a ≫ eI.hom) ≫ k₀ (p + 1) ≫ (eQ.hom ≫ h') :=
            congrArg₂ (fun v w => v ≫ k₀ (p + 1) ≫ w) hI hQ
          _ = _ := by simp only [Category.assoc]
      exact hE.trans ((congrArg ULift.up hComp).trans
        ((congrArg (fun v => ULift.up (a ≫ v.down ≫ h')) hz).symm.trans hτ.symm))
    exact hLeft.trans (hValue.trans hRight.symm)

/-- Let C be an abelian category with object universe u and morphism universe v. Let f : P′ → P and
g : Q → Q′ be integer chain and cochain maps, respectively, and let n ∈ ℤ. Assume all
differential images of P and P′ are projective. For m=n+1, the image-complex cohomology
comparisons to ∏ₚ Hom(Bₚ,H^{n-p}(Q)) commute with the actual induced image map of f and the
homology maps H^{n-p}(g). -/
lemma homUctImagesCohomologyIso_naturality {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q')
    (n m : ℤ) (hnm : n + 1 = m)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₁ m) ≫
        (homUctImagesCohomologyIso P' Q' n m hnm hI').hom =
      (homUctImagesCohomologyIso P Q n m hnm hI).hom ≫
        (homUctProductPresentationMap f
          (fun p => HomologicalComplex.homologyMap g (n - p))).τ₂ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let Z := homCochainComplex (outgoingImageZeroComplex P) Q
  let Z' := homCochainComplex (outgoingImageZeroComplex P') Q'
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (m - p))
  let G' : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P').X p ⟶ Q'.homology (m - p))
  let T : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂
  let T' : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P' (fun p => Q'.homology (n - p))).X₂
  let fI : outgoingImageZeroComplex P' ⟶ outgoingImageZeroComplex P :=
    ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₃
  let hOut (p : ℤ) : Projective ((outgoingImageZeroComplex P).X p) := by
    change Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))
    rw [nextDownInt p]
    exact hI p
  let hOut' (p : ℤ) : Projective ((outgoingImageZeroComplex P').X p) := by
    change Projective (Abelian.image (P'.d p ((ComplexShape.down ℤ).next p)))
    rw [nextDownInt p]
    exact hI' p
  let c : Z.homology m ≅ G :=
    homZeroSourceCohomologyIso (outgoingImageZeroComplex P) Q m (by intro i j; rfl) hOut
  let c' : Z'.homology m ≅ G' :=
    homZeroSourceCohomologyIso (outgoingImageZeroComplex P') Q' m (by intro i j; rfl) hOut'
  let t : U.obj G ≅ T := homUctImageProductIso P Q n m hnm
  let t' : U.obj G' ≅ T' := homUctImageProductIso P' Q' n m hnm
  let e : U.obj (Z.homology m) ≅ T := homUctImagesCohomologyIso P Q n m hnm hI
  let e' : U.obj (Z'.homology m) ≅ T' := homUctImagesCohomologyIso P' Q' n m hnm hI'
  let b : G ⟶ G' := homCohomologyProductMap fI g m
  let τ : T ⟶ T' := (homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - p))).τ₂
  let a : U.obj (Z.homology m) ⟶ U.obj (Z'.homology m) :=
    U.map (HomologicalComplex.homologyMap (homCyclesSequenceMap f g).τ₁ m)
  let a₀ : U.obj (Z.homology m) ⟶ U.obj (Z'.homology m) :=
    U.map (HomologicalComplex.homologyMap (homCochainComplexMap fI g) m)
  have ha : a = a₀ := congrArg (fun k => U.map (HomologicalComplex.homologyMap k m))
    (homCyclesSequenceMap_τ₁ f g)
  have he : e.hom = U.map c.hom ≫ t.hom := rfl
  have he' : e'.hom = U.map c'.hom ≫ t'.hom := rfl
  have hLift : U.map b ≫ t'.hom = t.hom ≫ τ := imageProduct_naturality f g n m hnm
  have hNative : a₀ ≫ U.map c'.hom = U.map c.hom ≫ U.map b :=
    (U.map_comp _ _).symm.trans
      ((congrArg (fun h => U.map h)
        (homZeroSourceCohomologyIso_naturality fI g m
          (by intro i j; rfl) (by intro i j; rfl) hOut hOut')).trans (U.map_comp _ _))
  change a ≫ e'.hom = e.hom ≫ τ
  calc
    _ = a₀ ≫ (U.map c'.hom ≫ t'.hom) := congrArg₂ (fun f g => f ≫ g) ha he'
    _ = (U.map c.hom ≫ U.map b) ≫ t'.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ t'.hom) hNative)
    _ = U.map c.hom ≫ (t.hom ≫ τ) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => U.map c.hom ≫ f) hLift)
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ τ) he.symm)

omit [HasExt.{w} C] in
private lemma imageEq_inv_boundary (P : ChainComplex C ℤ) (p i j : ℤ) (h : i = j) :
    eqToHom (congrArg (fun r => Abelian.image (P.d p r)) h.symm) ≫
        boundaryCyclesMap P p i ≫ eqToHom (congrArg (fun k : ℤ => (P.cycles k : C)) h) =
      boundaryCyclesMap P p j := by
  subst j
  let b : Abelian.image (P.d p i) ⟶ P.cycles i := boundaryCyclesMap P p i
  simp only [eqToHom_refl]
  change (𝟙 (Abelian.image (P.d p i))) ≫ b ≫ 𝟙 (P.cycles i) = b
  exact (Category.id_comp (b ≫ 𝟙 (P.cycles i))).trans (Category.comp_id b)

omit [HasExt.{w} C] in
private lemma cyclesHomologyFamily_eq (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (k : ∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
    {i j : ℤ} (h : i = j) :
    eqToHom (congrArg (fun k : ℤ => (P.cycles k : C)) h) ≫ k j =
      k i ≫ eqToHom (congrArg (fun p : ℤ => (Q.homology (n - p) : C)) h) := by
  subst j
  let f : P.cycles i ⟶ Q.homology (n - i) := k i
  simp only [eqToHom_refl]
  change (𝟙 (P.cycles i)) ≫ f = f ≫ 𝟙 (Q.homology (n - i))
  exact (Category.id_comp f).trans (Category.comp_id f).symm

private lemma boundaryProduct_reindex (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (k : ∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p)) (p : ℤ) :
    (homUctImageProductIso P Q n (n + 1) rfl).hom
        (ULift.up (homCyclesBoundaryProductMap P Q n k)) p =
      ULift.up ((n + 1).negOnePow • (boundaryCyclesMap P (p + 1) p ≫ k p)) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let B : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, (outgoingImageZeroComplex P).X p ⟶ Q.homology (n + 1 - p))
  let T : AddCommGrpCat.{max v w} :=
    (homUctProductPresentation P (fun p => Q.homology (n - p))).X₂
  let m : G ⟶ B := homCyclesBoundaryProductMap P Q n
  let E : U.obj B ≅ T := homUctImageProductIso P Q n (n + 1) rfl
  let k₀ : G := k
  let z : B := m.hom k₀
  let r := (p + 1) - 1
  have hr : r = p := by dsimp only [r]; omega
  have hNext : (ComplexShape.down ℤ).next (p + 1) = p :=
    (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (p + 1) p (by omega))
  let eI : (homUctBoundaryPresentation P p).X₁ ≅
      (outgoingImageZeroComplex P).X (p + 1) :=
    eqToIso (congrArg (fun i => Abelian.image (P.d (p + 1) i)) hNext.symm)
  let κ : (homUctBoundaryPresentation P p).X₁ ⟶ (outgoingImageZeroComplex P).X (p + 1) :=
    eI.hom
  let β : (outgoingImageZeroComplex P).X (p + 1) ⟶ P.cycles r :=
    homCyclesBoundaryComponent P (p + 1)
  let β₀ : (outgoingImageZeroComplex P).X (p + 1) ⟶
      P.cycles ((ComplexShape.down ℤ).next (p + 1)) :=
    boundaryCyclesMap P (p + 1) ((ComplexShape.down ℤ).next (p + 1))
  let c₁ : P.cycles ((ComplexShape.down ℤ).next (p + 1)) ⟶ P.cycles r :=
    eqToHom (congrArg (fun i : ℤ => (P.cycles i : C)) (nextDownInt (p + 1)))
  let c : P.cycles r ⟶ P.cycles p :=
    eqToHom (congrArg (fun i : ℤ => (P.cycles i : C)) hr)
  let c₀ : P.cycles ((ComplexShape.down ℤ).next (p + 1)) ⟶ P.cycles p :=
    eqToHom (congrArg (fun i : ℤ => (P.cycles i : C)) hNext)
  have hβ : β = β₀ ≫ c₁ := rfl
  have hc : c₁ ≫ c = c₀ := by
    dsimp only [c₁, c, c₀]
    rw [eqToHom_trans]
  have hBoundary : κ ≫ β ≫ c = boundaryCyclesMap P (p + 1) p := by
    have hFirst : κ ≫ β ≫ c = κ ≫ (β₀ ≫ c₁) ≫ c :=
      congrArg (fun a : (outgoingImageZeroComplex P).X (p + 1) ⟶ P.cycles r =>
        κ ≫ a ≫ c) hβ
    have hAssoc : κ ≫ (β₀ ≫ c₁) ≫ c = κ ≫ β₀ ≫ (c₁ ≫ c) :=
      congrArg (fun a : (outgoingImageZeroComplex P).X (p + 1) ⟶ P.cycles p =>
        κ ≫ a) (Category.assoc β₀ c₁ c)
    have hCast : κ ≫ β₀ ≫ (c₁ ≫ c) = κ ≫ β₀ ≫ c₀ :=
      congrArg (fun a : P.cycles ((ComplexShape.down ℤ).next (p + 1)) ⟶ P.cycles p =>
        κ ≫ β₀ ≫ a) hc
    have hFinal : κ ≫ β₀ ≫ c₀ = boundaryCyclesMap P (p + 1) p := by
      dsimp only [κ, eI, β₀, c₀]
      exact imageEq_inv_boundary P (p + 1) ((ComplexShape.down ℤ).next (p + 1)) p hNext
    exact hFirst.trans (hAssoc.trans (hCast.trans hFinal))
  let a₁ : Q.homology (n - r) ⟶ Q.homology (n + 1 - (p + 1)) :=
    eqToHom (congrArg (fun i : ℤ => (Q.homology i : C)) (by dsimp only [r]; omega))
  let a₂ : Q.homology (n + 1 - (p + 1)) ⟶ Q.homology (n - p) :=
    eqToHom (congrArg (fun i : ℤ => (Q.homology i : C)) (by omega))
  let a : Q.homology (n - r) ⟶ Q.homology (n - p) :=
    eqToHom (congrArg (fun i : ℤ => (Q.homology (n - i) : C)) hr)
  have ha : a₁ ≫ a₂ = a := by
    dsimp only [a₁, a₂, a]
    rw [eqToHom_trans]
  have hFamily : c ≫ k p = k r ≫ a := cyclesHomologyFamily_eq P Q n k hr
  have hz : z (p + 1) = (n + 1).negOnePow • (β ≫ k r ≫ a₁) := rfl
  have hE : E.hom.hom (ULift.up z) p = ULift.up (κ ≫ z (p + 1) ≫ a₂) :=
    homUctImageProductIso_hom_up P Q n (n + 1) rfl z p
  have hValue : κ ≫ z (p + 1) ≫ a₂ =
      (n + 1).negOnePow • (boundaryCyclesMap P (p + 1) p ≫ k p) := by
    calc
      _ = κ ≫ ((n + 1).negOnePow • (β ≫ k r ≫ a₁)) ≫ a₂ :=
        congrArg (fun x => κ ≫ x ≫ a₂) hz
      _ = (n + 1).negOnePow • (κ ≫ β ≫ k r ≫ (a₁ ≫ a₂)) := by
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
      _ = (n + 1).negOnePow • (κ ≫ β ≫ (c ≫ k p)) :=
        congrArg (fun x => (n + 1).negOnePow • (κ ≫ β ≫ x))
          ((congrArg (fun x => k r ≫ x) ha).trans hFamily.symm)
      _ = (n + 1).negOnePow • ((κ ≫ β ≫ c) ≫ k p) := by
        simp only [Category.assoc]
      _ = _ := congrArg (fun x => (n + 1).negOnePow • (x ≫ k p)) hBoundary
  change E.hom.hom (ULift.up z) p = _
  exact hE.trans (congrArg ULift.up hValue)

omit [HasExt.{w} C] in
private lemma connecting_degree_eq (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homCyclesSequence_shortExact P Q hI).δ n m (ComplexShape.up_mk n m hnm) =
      homCyclesConnecting P Q n hI ≫
        eqToHom (congrArg (fun i : ℤ =>
          (homCochainComplex (outgoingImageZeroComplex P) Q).homology i) hnm) := by
  subst m
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let d : G.homology n ⟶ F.homology (n + 1) := homCyclesConnecting P Q n hI
  change d = d ≫ 𝟙 (F.homology (n + 1))
  exact (Category.comp_id d).symm

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Zₚ(P) is projective, and let m=n+1. Under
the cycles and image full-product cohomology comparisons, the connecting map Hⁿ Hom(Z⁰(P),Q) →
Hᵐ Hom(I⁰(P),Q) is (-1)^m times βₚ-precomposition on ∏ₚ Hom(Zₚ(P),H^{n-p}(Q)). The positive
Hom–Ext presentation map is otherwise unchanged. -/
lemma homUctConnecting_square (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n m : ℤ) (hnm : n + 1 = m)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    let A := homUctProductPresentation P (fun p => Q.homology (n - p))
    let ε : A.X₁ ≅ A.X₁ :=
      (DistribMulAction.toAddEquiv A.X₁ (n + 1).negOnePow).toAddCommGrpIso
    AddCommGrpCat.uliftFunctor.{w, v}.map
        ((homCyclesSequence_shortExact P Q hI).δ n m (ComplexShape.up_mk n m hnm)) ≫
        (homUctImagesCohomologyIso P Q n m hnm hI).hom =
      (homUctCyclesCohomologyIso P Q n hZ).hom ≫ ε.hom ≫ A.f := by
  subst m
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let Z := cyclesZeroComplex P
  let I := outgoingImageZeroComplex P
  let K := homCochainComplex Z Q
  let L := homCochainComplex I Q
  let G : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, P.cycles p ⟶ Q.homology (n - p))
  let T : AddCommGrpCat.{v} := AddCommGrpCat.of
    (∀ p : ℤ, I.X p ⟶ Q.homology (n + 1 - p))
  let hOut (p : ℤ) : Projective ((outgoingImageZeroComplex P).X p) := by
    change Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))
    rw [nextDownInt p]
    exact hI p
  let hCycles (p : ℤ) : Projective ((cyclesZeroComplex P).X p) := by
    change Projective (P.cycles p)
    exact hZ p
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - p))
  let ε : A.X₁ ≅ A.X₁ :=
    (DistribMulAction.toAddEquiv A.X₁ (n + 1).negOnePow).toAddCommGrpIso
  let tG : U.obj G ≅ A.X₁ := AddCommGrpCat.uliftIntPiIso
    (fun p : ℤ => AddCommGrpCat.of (P.cycles p ⟶ Q.homology (n - p)))
  let tI : U.obj T ≅ A.X₂ := homUctImageProductIso P Q n (n + 1) rfl
  let b : G ⟶ T := homCyclesBoundaryProductMap P Q n
  let cG : K.homology n ≅ G :=
    homZeroSourceCohomologyIso Z Q n (by intro i j; rfl) hCycles
  let cI : L.homology (n + 1) ≅ T :=
    homZeroSourceCohomologyIso I Q (n + 1) (by intro i j; rfl) hOut
  let eG : U.obj (K.homology n) ≅ A.X₁ := homUctCyclesCohomologyIso P Q n hZ
  let eI : U.obj (L.homology (n + 1)) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q n (n + 1) rfl hI
  let d : K.homology n ⟶ L.homology (n + 1) := homCyclesConnecting P Q n hI
  let qG : K.homology n ⟶ G :=
    homZeroSourceCohomologyComparison Z Q n (by intro i j; rfl)
  let qI : L.homology (n + 1) ⟶ T :=
    homZeroSourceCohomologyComparison I Q (n + 1) (by intro i j; rfl)
  have heG : eG.hom = U.map cG.hom ≫ tG.hom := rfl
  have heI : eI.hom = U.map cI.hom ≫ tI.hom := rfl
  have hProd : U.map b ≫ tI.hom = tG.hom ≫ ε.hom ≫ A.f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro k
    cases k with
    | up k =>
      let k₀ : G := k
      let z : A.X₁ := tG.hom.hom (ULift.up k₀)
      let zε : A.X₁ := ε.hom.hom z
      have hMap : (U.map b).hom (ULift.up k₀) = ULift.up (b.hom k₀) := rfl
      have hLeft : (U.map b ≫ tI.hom).hom (ULift.up k₀) =
          tI.hom.hom (ULift.up (b.hom k₀)) :=
        (AddCommGrpCat.comp_apply (U.map b) tI.hom (ULift.up k₀)).trans
          (congrArg (fun x => tI.hom.hom x) hMap)
      have hRight : (tG.hom ≫ ε.hom ≫ A.f).hom (ULift.up k₀) = A.f.hom zε :=
        (AddCommGrpCat.comp_apply tG.hom (ε.hom ≫ A.f) (ULift.up k₀)).trans
          (AddCommGrpCat.comp_apply ε.hom A.f z)
      have hValue : tI.hom.hom (ULift.up (b.hom k₀)) = A.f.hom zε := by
        funext p
        let a : (homUctBoundaryPresentation P p).X₁ ⟶ P.cycles p :=
          boundaryCyclesMap P (p + 1) p
        have hz : z p = ULift.up (k₀ p) :=
          AddCommGrpCat.uliftIntPiIso_hom_up
            (fun p : ℤ => AddCommGrpCat.of (P.cycles p ⟶ Q.homology (n - p))) k₀ p
        have hε : zε p = (n + 1).negOnePow • z p := rfl
        have hεp : zε p = ULift.up ((n + 1).negOnePow • k₀ p) :=
          hε.trans ((congrArg (fun x => (n + 1).negOnePow • x) hz).trans (by rfl))
        have hRaw : tI.hom.hom (ULift.up (b.hom k₀)) p =
            ULift.up ((n + 1).negOnePow • (a ≫ k₀ p)) :=
          boundaryProduct_reindex P Q n k₀ p
        have hA : A.f.hom zε p = ULift.up (a ≫ (zε p).down) :=
          homUctProductPresentation_f_apply P (fun p => Q.homology (n - p)) zε p
        have hDown : (zε p).down = (n + 1).negOnePow • k₀ p :=
          congrArg (fun x : ULift.{w, v} (P.cycles p ⟶ Q.homology (n - p)) => x.down) hεp
        have hScalar : (n + 1).negOnePow • (a ≫ k₀ p) =
            a ≫ ((n + 1).negOnePow • k₀ p) := (Linear.comp_units_smul _ _ _).symm
        exact hRaw.trans ((congrArg ULift.up hScalar).trans
          ((congrArg (fun x => ULift.up (a ≫ x)) hDown.symm).trans hA.symm))
      exact hLeft.trans (hValue.trans hRight.symm)
  have hcG : cG.hom = qG :=
    homZeroSourceCohomologyIso_hom Z Q n (by intro i j; rfl) hCycles
  have hcI : cI.hom = qI :=
    homZeroSourceCohomologyIso_hom I Q (n + 1) (by intro i j; rfl) hOut
  have hSquare : d ≫ qI = qG ≫ b := homCyclesConnecting_productSquare P Q n hI
  have hNative : d ≫ cI.hom = cG.hom ≫ b :=
    (congrArg (fun a => d ≫ a) hcI).trans
      (hSquare.trans (congrArg (fun a => a ≫ b) hcG.symm))
  have hMapped : U.map d ≫ U.map cI.hom = U.map cG.hom ≫ U.map b :=
    (U.map_comp d cI.hom).symm.trans
      ((congrArg U.map hNative).trans (U.map_comp cG.hom b))
  have hResult : U.map d ≫ eI.hom = eG.hom ≫ ε.hom ≫ A.f := by
    calc
      _ = U.map d ≫ (U.map cI.hom ≫ tI.hom) := congrArg (fun a => U.map d ≫ a) heI
      _ = (U.map d ≫ U.map cI.hom) ≫ tI.hom := (Category.assoc _ _ _).symm
      _ = (U.map cG.hom ≫ U.map b) ≫ tI.hom := congrArg (fun a => a ≫ tI.hom) hMapped
      _ = U.map cG.hom ≫ (U.map b ≫ tI.hom) := Category.assoc _ _ _
      _ = U.map cG.hom ≫ (tG.hom ≫ ε.hom ≫ A.f) :=
        congrArg (fun a => U.map cG.hom ≫ a) hProd
      _ = (U.map cG.hom ≫ tG.hom) ≫ ε.hom ≫ A.f := by simp only [Category.assoc]
      _ = _ := congrArg (fun a => a ≫ ε.hom ≫ A.f) heG.symm
  let δ : K.homology n ⟶ L.homology (n + 1) :=
    (homCyclesSequence_shortExact P Q hI).δ n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)
  have hδ : δ = d := rfl
  change U.map δ ≫ eI.hom = eG.hom ≫ ε.hom ≫ A.f
  exact (congrArg (fun a => U.map a ≫ eI.hom) hδ).trans hResult

private lemma unitIso_naturality {A B : AddCommGrpCat.{max v w}} (f : A ⟶ B) (u : ℤˣ) :
    (DistribMulAction.toAddEquiv A u).toAddCommGrpIso.hom ≫ f =
      f ≫ (DistribMulAction.toAddEquiv B u).toAddCommGrpIso.hom := by
  apply AddCommGrpCat.ext
  intro x
  change f.hom ((u : ℤ) • x) = (u : ℤ) • f.hom x
  exact f.hom.map_zsmul (u : ℤ) x

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
Assume every Zₚ(P) is projective and Ext_C is available in universe w. Normalizing the domain
unit (-1)^n identifies coker(δₙ₋₁) with ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), with positive Yoneda
extension representatives. -/
def homUctCokernelIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    (homCyclesCohomologyClip.{u, v, w} P Q n hI).X₁ ≅
      (homUctProductPresentation P (fun p => Q.homology (n - 1 - p))).X₃ := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - 1 - p))
  let d : U.obj (G.homology (n - 1)) ⟶ U.obj (F.homology n) :=
    U.map ((homCyclesSequence_shortExact P Q hI).δ (n - 1) n
      (ComplexShape.up_mk (n - 1) n (by omega)))
  let ε : A.X₁ ≅ A.X₁ :=
    (DistribMulAction.toAddEquiv A.X₁ ((n - 1) + 1).negOnePow).toAddCommGrpIso
  let a : U.obj (G.homology (n - 1)) ≅ A.X₁ :=
    homUctCyclesCohomologyIso P Q (n - 1) hZ ≪≫ ε
  let b : U.obj (F.homology n) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
  have h : d ≫ b.hom = a.hom ≫ A.f :=
    homUctConnecting_square P Q (n - 1) n (by omega) hI hZ
  let m : cokernel d ≅ cokernel A.f := cokernel.mapIso d A.f a b h
  let t : cokernel A.f ≅ A.X₃ :=
    homUctPresentationCokernelIso P (fun p => Q.homology (n - 1 - p)) hZ
  change cokernel d ≅ A.X₃
  exact m ≪≫ t

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
Assume all cycles are projective and Ext_C is available. The cokernel quotient of δₙ₋₁ followed
by the product-Ext¹ comparison equals the image-complex cohomology comparison followed by the
positive product Yoneda connecting arrow. -/
@[reassoc]
lemma homUctCokernelIso_π_hom (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    cokernel.π (AddCommGrpCat.uliftFunctor.{w, v}.map
        ((homCyclesSequence_shortExact P Q hI).δ (n - 1) n
          (ComplexShape.up_mk (n - 1) n (by omega)))) ≫
        (homUctCokernelIso P Q n hI hZ).hom =
      (homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI).hom ≫
        (homUctProductPresentation P (fun p => Q.homology (n - 1 - p))).g := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - 1 - p))
  let d : U.obj (G.homology (n - 1)) ⟶ U.obj (F.homology n) :=
    U.map ((homCyclesSequence_shortExact P Q hI).δ (n - 1) n
      (ComplexShape.up_mk (n - 1) n (by omega)))
  let ε : A.X₁ ≅ A.X₁ :=
    (DistribMulAction.toAddEquiv A.X₁ ((n - 1) + 1).negOnePow).toAddCommGrpIso
  let a : U.obj (G.homology (n - 1)) ≅ A.X₁ :=
    homUctCyclesCohomologyIso P Q (n - 1) hZ ≪≫ ε
  let b : U.obj (F.homology n) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
  have h : d ≫ b.hom = a.hom ≫ A.f :=
    homUctConnecting_square P Q (n - 1) n (by omega) hI hZ
  let m : cokernel d ≅ cokernel A.f := cokernel.mapIso d A.f a b h
  let t : cokernel A.f ≅ A.X₃ :=
    homUctPresentationCokernelIso P (fun p => Q.homology (n - 1 - p)) hZ
  let E : cokernel d ≅ A.X₃ := homUctCokernelIso P Q n hI hZ
  let πd : U.obj (F.homology n) ⟶ cokernel d := cokernel.π d
  let πA : A.X₂ ⟶ cokernel A.f := cokernel.π A.f
  have hPack : E = m ≪≫ t := rfl
  have hPackHom : E.hom = m.hom ≫ t.hom :=
    congrArg (fun e : cokernel d ≅ A.X₃ => e.hom) hPack
  have hm : πd ≫ m.hom = b.hom ≫ πA := by
    dsimp only [m, cokernel.mapIso, cokernel.map]
    exact cokernel.π_desc _ _ _
  have ht : πA ≫ t.hom = A.g :=
    homUctPresentationCokernelIso_π_hom P (fun p => Q.homology (n - 1 - p)) hZ
  change πd ≫ E.hom = b.hom ≫ A.g
  exact (congrArg (fun f => πd ≫ f) hPackHom).trans
    ((Category.assoc πd m.hom t.hom).symm.trans
      ((congrArg (fun f => f ≫ t.hom) hm).trans
        ((Category.assoc b.hom πA t.hom).trans (congrArg (fun f => b.hom ≫ f) ht))))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
Assume every Zₚ(P) is projective. Normalizing the codomain unit (-1)^{n+1} identifies ker(δₙ)
with the full product ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), using the original homology quotients. -/
def homUctKernelIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    (homCyclesCohomologyClip.{u, v, w} P Q n hI).X₃ ≅
      AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p))) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - p))
  let T : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)))
  let d : U.obj (G.homology n) ⟶ U.obj (F.homology (n + 1)) :=
    U.map ((homCyclesSequence_shortExact P Q hI).δ n (n + 1)
      (ComplexShape.up_mk n (n + 1) rfl))
  let f : A.X₁ ⟶ A.X₂ := A.f
  let ε₁ : A.X₁ ≅ A.X₁ :=
    (DistribMulAction.toAddEquiv A.X₁ (n + 1).negOnePow).toAddCommGrpIso
  let ε₂ : A.X₂ ≅ A.X₂ :=
    (DistribMulAction.toAddEquiv A.X₂ (n + 1).negOnePow).toAddCommGrpIso
  let a : U.obj (G.homology n) ≅ A.X₁ := homUctCyclesCohomologyIso P Q n hZ
  let b₀ : U.obj (F.homology (n + 1)) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q n (n + 1) rfl hI
  let b : U.obj (F.homology (n + 1)) ≅ A.X₂ := b₀ ≪≫ ε₂.symm
  have h₁ : d ≫ b₀.hom = a.hom ≫ ε₁.hom ≫ f :=
    homUctConnecting_square P Q n (n + 1) rfl hI hZ
  have h₂ : ε₁.hom ≫ f = f ≫ ε₂.hom := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change f.hom (((n + 1).negOnePow : ℤ) • x) =
      ((n + 1).negOnePow : ℤ) • f.hom x
    exact f.hom.map_zsmul ((n + 1).negOnePow : ℤ) x
  have hb : b.hom = b₀.hom ≫ ε₂.inv := rfl
  have h : d ≫ b.hom = a.hom ≫ f := by
    calc
      _ = (d ≫ b₀.hom) ≫ ε₂.inv :=
        (congrArg (fun g => d ≫ g) hb).trans (Category.assoc d b₀.hom ε₂.inv).symm
      _ = (a.hom ≫ (ε₁.hom ≫ f)) ≫ ε₂.inv :=
        congrArg (fun g => g ≫ ε₂.inv) h₁
      _ = a.hom ≫ ((ε₁.hom ≫ f) ≫ ε₂.inv) := Category.assoc _ _ _
      _ = a.hom ≫ ((f ≫ ε₂.hom) ≫ ε₂.inv) :=
        congrArg (fun g => a.hom ≫ (g ≫ ε₂.inv)) h₂
      _ = a.hom ≫ (f ≫ (ε₂.hom ≫ ε₂.inv)) :=
        congrArg (fun g => a.hom ≫ g) (Category.assoc f ε₂.hom ε₂.inv)
      _ = a.hom ≫ f :=
        (congrArg (fun g => a.hom ≫ (f ≫ g)) ε₂.hom_inv_id).trans
          (congrArg (fun g => a.hom ≫ g) (Category.comp_id f))
  let m : kernel d ≅ kernel f := kernel.mapIso d f a b h
  let t : kernel f ≅ T := homUctHomKernelIso P (fun p => Q.homology (n - p))
  change kernel d ≅ T
  exact m ≪≫ t

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. The Hom short exact sequence is 0 → Hom(I⁰(P),Q) → Hom(P,Q)
→ Hom(Z⁰(P),Q) → 0. Write δₖ : Hᵏ Hom(Z⁰(P),Q) → H^{k+1} Hom(I⁰(P),Q) for its connecting map.
Assume every Zₚ(P) is projective. The kernel-to-product-Hom comparison followed by
πₚ-precomposition equals the inclusion into Hⁿ Hom(Z⁰(P),Q) followed by the cycles full-product
cohomology comparison. -/
@[reassoc]
lemma homUctKernelIso_hom_inclusion (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hZ : ∀ p : ℤ, Projective (P.cycles p)) :
    (homUctKernelIso P Q n hI hZ).hom ≫
        homUctHomKernelInclusion P (fun p => Q.homology (n - p)) =
      kernel.ι (AddCommGrpCat.uliftFunctor.{w, v}.map
        ((homCyclesSequence_shortExact P Q hI).δ n (n + 1) (ComplexShape.up_mk n (n + 1) rfl))) ≫
        (homUctCyclesCohomologyIso P Q n hZ).hom := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - p))
  let T : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)))
  let d : U.obj (G.homology n) ⟶ U.obj (F.homology (n + 1)) :=
    U.map ((homCyclesSequence_shortExact P Q hI).δ n (n + 1)
      (ComplexShape.up_mk n (n + 1) rfl))
  let f : A.X₁ ⟶ A.X₂ := A.f
  let ε₁ : A.X₁ ≅ A.X₁ :=
    (DistribMulAction.toAddEquiv A.X₁ (n + 1).negOnePow).toAddCommGrpIso
  let ε₂ : A.X₂ ≅ A.X₂ :=
    (DistribMulAction.toAddEquiv A.X₂ (n + 1).negOnePow).toAddCommGrpIso
  let a : U.obj (G.homology n) ≅ A.X₁ := homUctCyclesCohomologyIso P Q n hZ
  let b₀ : U.obj (F.homology (n + 1)) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q n (n + 1) rfl hI
  let b : U.obj (F.homology (n + 1)) ≅ A.X₂ := b₀ ≪≫ ε₂.symm
  have h₁ : d ≫ b₀.hom = a.hom ≫ ε₁.hom ≫ f :=
    homUctConnecting_square P Q n (n + 1) rfl hI hZ
  have h₂ : ε₁.hom ≫ f = f ≫ ε₂.hom := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change f.hom (((n + 1).negOnePow : ℤ) • x) =
      ((n + 1).negOnePow : ℤ) • f.hom x
    exact f.hom.map_zsmul ((n + 1).negOnePow : ℤ) x
  have hb : b.hom = b₀.hom ≫ ε₂.inv := rfl
  have h : d ≫ b.hom = a.hom ≫ f := by
    have hFirst : d ≫ b.hom = (d ≫ b₀.hom) ≫ ε₂.inv :=
      (congrArg (fun t : U.obj (F.homology (n + 1)) ⟶ A.X₂ => d ≫ t) hb).trans
        (Category.assoc d b₀.hom ε₂.inv).symm
    have hSquare : (d ≫ b₀.hom) ≫ ε₂.inv =
        (a.hom ≫ ε₁.hom ≫ f) ≫ ε₂.inv :=
      congrArg (fun t : U.obj (G.homology n) ⟶ A.X₂ => t ≫ ε₂.inv) h₁
    have hAssoc : (a.hom ≫ ε₁.hom ≫ f) ≫ ε₂.inv =
        a.hom ≫ ((ε₁.hom ≫ f) ≫ ε₂.inv) :=
      Category.assoc a.hom (ε₁.hom ≫ f) ε₂.inv
    have hUnit : a.hom ≫ ((ε₁.hom ≫ f) ≫ ε₂.inv) =
        a.hom ≫ ((f ≫ ε₂.hom) ≫ ε₂.inv) :=
      congrArg (fun t : A.X₁ ⟶ A.X₂ => a.hom ≫ (t ≫ ε₂.inv)) h₂
    have hPost : a.hom ≫ ((f ≫ ε₂.hom) ≫ ε₂.inv) =
        a.hom ≫ (f ≫ (ε₂.hom ≫ ε₂.inv)) :=
      congrArg (fun t : A.X₁ ⟶ A.X₂ => a.hom ≫ t)
        (Category.assoc f ε₂.hom ε₂.inv)
    have hCancel : a.hom ≫ (f ≫ (ε₂.hom ≫ ε₂.inv)) = a.hom ≫ f :=
      (congrArg (fun t : A.X₂ ⟶ A.X₂ => a.hom ≫ (f ≫ t)) ε₂.hom_inv_id).trans
        (congrArg (fun t : A.X₁ ⟶ A.X₂ => a.hom ≫ t) (Category.comp_id f))
    exact hFirst.trans (hSquare.trans (hAssoc.trans (hUnit.trans (hPost.trans hCancel))))
  let m : kernel d ≅ kernel f := kernel.mapIso d f a b h
  let t : kernel f ≅ T := homUctHomKernelIso P (fun p => Q.homology (n - p))
  let E : kernel d ≅ T := homUctKernelIso P Q n hI hZ
  let κ : T ⟶ A.X₁ := homUctHomKernelInclusion P (fun p => Q.homology (n - p))
  let ιd : kernel d ⟶ U.obj (G.homology n) := kernel.ι d
  let ιA : kernel f ⟶ A.X₁ := kernel.ι f
  have hPack : E = m ≪≫ t := rfl
  have hPackHom : E.hom = m.hom ≫ t.hom :=
    congrArg (fun e : kernel d ≅ T => e.hom) hPack
  have hm : m.hom ≫ ιA = ιd ≫ a.hom := by
    dsimp only [m, kernel.mapIso, kernel.map]
    exact kernel.lift_ι _ _ _
  have ht : t.hom ≫ κ = ιA :=
    homUctHomKernelIso_hom_inclusion P (fun p => Q.homology (n - p))
  change E.hom ≫ κ = ιd ≫ a.hom
  exact (congrArg (fun f => f ≫ κ) hPackHom).trans
    ((Category.assoc m.hom t.hom κ).trans
      ((congrArg (fun f => m.hom ≫ f) ht).trans hm))

omit [HasExt.{w} C] in
private lemma projectiveUctCycles (P : ChainComplex C ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ∀ p : ℤ, Projective (P.cycles p) := fun p => by
  letI : Projective (P.X p) := hP p
  letI : Projective (Abelian.image (P.d p ((ComplexShape.down ℤ).next p))) := by
    rw [nextDownInt p]
    exact hI p
  exact HomologicalComplex.projective_cycles P p

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
full-product UCT short complex is obtained from coker(δₙ₋₁) → Hⁿ Hom(P,Q) → ker(δₙ) by the
positive product-Ext¹ and product-Hom comparisons. Its left map is the Hom-sequence inclusion
after the inverse Ext comparison; its right map is the Hom-sequence restriction followed by the
Hom comparison. -/
def homUniversalCoefficientSequenceEngine (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ShortComplex AddCommGrpCat.{max v w} := by
  let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
  let S : ShortComplex AddCommGrpCat.{max v w} := homCyclesCohomologyClip P Q n hI
  let E : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{v, w} (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1))
  let M : AddCommGrpCat.{max v w} :=
    AddCommGrpCat.uliftFunctor.{w, v}.obj ((homCochainComplex P Q).homology n)
  let H : AddCommGrpCat.{max v w} := AddCommGrpCat.of
    (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)))
  let e₁ : S.X₁ ≅ E := homUctCokernelIso P Q n hI hZ
  let e₃ : S.X₃ ≅ H := homUctKernelIso P Q n hI hZ
  let f : E ⟶ M := e₁.inv ≫ S.f
  let g : M ⟶ H := S.g ≫ e₃.hom
  have hfg : f ≫ g = 0 := by
    change (e₁.inv ≫ S.f) ≫ (S.g ≫ e₃.hom) = 0
    calc
      _ = e₁.inv ≫ (S.f ≫ S.g) ≫ e₃.hom := by simp only [Category.assoc]
      _ = 0 := (congrArg (fun a => e₁.inv ≫ a ≫ e₃.hom) S.zero).trans
        (by simp only [Limits.comp_zero, Limits.zero_comp])
  exact ShortComplex.mk f g hfg

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
left object is exactly the full product ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), with each Ext factor
moved to universe max(v,w). -/
lemma homUniversalCoefficientSequenceEngine_X₁ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngine P Q n hP hI).X₁ =
      AddCommGrpCat.of (∀ p : ℤ,
        ULift.{v, w} (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1)) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
middle object is Hⁿ Hom(P,Q), moved to universe max(v,w). The full Hom product keeps the given
differentials of P and Q. -/
lemma homUniversalCoefficientSequenceEngine_X₂ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngine P Q n hP hI).X₂ =
      AddCommGrpCat.uliftFunctor.{w, v}.obj ((homCochainComplex P Q).homology n) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
right object is exactly the full product ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with the individual Hom
factors moved to universe max(v,w). -/
lemma homUniversalCoefficientSequenceEngine_X₃ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngine P Q n hP hI).X₃ =
      AddCommGrpCat.of (∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p))) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
canonical cokernel-to-Ext and kernel-to-Hom endpoint comparisons give an isomorphism of the
clipped Hom cohomology sequence with this full-product UCT short complex; the middle cohomology
object is unchanged. -/
def homUniversalCoefficientSequenceEngineIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    homCyclesCohomologyClip.{u, v, w} P Q n hI ≅
      homUniversalCoefficientSequenceEngine P Q n hP hI := by
  let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
  let S : ShortComplex AddCommGrpCat.{max v w} := homCyclesCohomologyClip P Q n hI
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let M : AddCommGrpCat.{max v w} :=
    AddCommGrpCat.uliftFunctor.{w, v}.obj ((homCochainComplex P Q).homology n)
  let e₁ : S.X₁ ≅ T.X₁ := homUctCokernelIso P Q n hI hZ
  let e₂ : S.X₂ ≅ T.X₂ := Iso.refl M
  let e₃ : S.X₃ ≅ T.X₃ := homUctKernelIso P Q n hI hZ
  have hf : T.f = e₁.inv ≫ S.f := rfl
  have hg : T.g = S.g ≫ e₃.hom := rfl
  have he₂ : e₂.hom = 𝟙 M := rfl
  let sF : S.X₁ ⟶ M := S.f
  let sG : M ⟶ S.X₃ := S.g
  let tF : T.X₁ ⟶ M := T.f
  let tG : M ⟶ T.X₃ := T.g
  let idM : M ⟶ M := e₂.hom
  have hfM : tF = e₁.inv ≫ sF := hf
  have hgM : tG = sG ≫ e₃.hom := hg
  have heM : idM = 𝟙 M := he₂
  change S ≅ T
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · change e₁.hom ≫ tF = sF ≫ idM
    have hFirst : e₁.hom ≫ tF = e₁.hom ≫ (e₁.inv ≫ sF) :=
      congrArg (fun t : T.X₁ ⟶ M => e₁.hom ≫ t) hfM
    have hAssoc : e₁.hom ≫ (e₁.inv ≫ sF) = (e₁.hom ≫ e₁.inv) ≫ sF :=
      (Category.assoc e₁.hom e₁.inv sF).symm
    have hCancel : (e₁.hom ≫ e₁.inv) ≫ sF = sF :=
      (congrArg (fun t : S.X₁ ⟶ S.X₁ => t ≫ sF) e₁.hom_inv_id).trans
        (Category.id_comp sF)
    have hIdentity : sF = sF ≫ idM :=
      (Category.comp_id sF).symm.trans
        (congrArg (fun t : M ⟶ M => sF ≫ t) heM.symm)
    exact hFirst.trans (hAssoc.trans (hCancel.trans hIdentity))
  · change idM ≫ tG = sG ≫ e₃.hom
    have hFirst : idM ≫ tG = (𝟙 M) ≫ (sG ≫ e₃.hom) :=
      congrArg₂ (fun t : M ⟶ M => fun v : M ⟶ T.X₃ => t ≫ v) heM hgM
    exact hFirst.trans (Category.id_comp (sG ≫ e₃.hom))

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. There
is a short exact sequence 0 → ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) → Hⁿ Hom(P,Q) → ∏ₚ
Hom_C(Hₚ(P),H^{n-p}(Q)) → 0 in the common group universe max(v,w). The left map is the positive
Yoneda-extension comparison followed by the Hom long-exact-sequence inclusion; the right map is
cycles restriction followed by the homology-Hom comparison. Both projectivity families are used
to obtain projective cycles; Q is arbitrary. -/
lemma homUniversalCoefficientSequenceEngine_shortExact (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngine P Q n hP hI).ShortExact :=
  ShortComplex.shortExact_of_iso (homUniversalCoefficientSequenceEngineIso P Q n hP hI)
    (homCyclesCohomologyClip_shortExact P Q n hI)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. A
class in Hⁿ Hom(I⁰(P),Q) first gives its full positive Yoneda Ext¹ family and then maps by the
left UCT injection to Hⁿ Hom(P,Q). This composite is exactly the cohomology map induced by the
Hom inclusion Hom(I⁰(P),Q) → Hom(P,Q). -/
@[reassoc]
lemma homUniversalCoefficientSequenceEngine_left_representative (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI).hom ≫
        (homUctProductPresentation P (fun p => Q.homology (n - 1 - p))).g ≫
        (homUniversalCoefficientSequenceEngine P Q n hP hI).f =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCyclesSequence P Q).f n) := by
  let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let S : ShortComplex AddCommGrpCat.{max v w} := homCyclesCohomologyClip P Q n hI
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - 1 - p))
  let e₁ : S.X₁ ≅ T.X₁ := homUctCokernelIso P Q n hI hZ
  let b : U.obj (F.homology n) ≅ A.X₂ :=
    homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
  let d : U.obj (G.homology (n - 1)) ⟶ U.obj (F.homology n) := U.map
    ((homCyclesSequence_shortExact P Q hI).δ (n - 1) n (ComplexShape.up_mk (n - 1) n (by omega)))
  let π : U.obj (F.homology n) ⟶ S.X₁ := cokernel.π d
  let a : U.obj (F.homology n) ⟶ S.X₂ :=
    U.map (HomologicalComplex.homologyMap (homCyclesSequence P Q).f n)
  have hπ : π ≫ e₁.hom = b.hom ≫ A.g :=
    homUctCokernelIso_π_hom P Q n hI hZ
  have hf : T.f = e₁.inv ≫ S.f := rfl
  have hClip : π ≫ S.f = a :=
    ComposableArrows.middleKernelCokernelSequence_π_f (homCyclesFourArrowSequence P Q n hI) _
  have hValue : (b.hom ≫ A.g) ≫ T.f = a := by
    calc
      _ = (π ≫ e₁.hom) ≫ (e₁.inv ≫ S.f) := congrArg₂ (fun x y => x ≫ y) hπ.symm hf
      _ = π ≫ (e₁.hom ≫ e₁.inv) ≫ S.f := by simp only [Category.assoc]
      _ = π ≫ S.f := (congrArg (fun x => π ≫ x ≫ S.f) e₁.hom_inv_id).trans
        (congrArg (fun x => π ≫ x) (Category.id_comp S.f))
      _ = a := hClip
  change b.hom ≫ A.g ≫ T.f = a
  exact (Category.assoc b.hom A.g T.f).symm.trans hValue

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also that every Pₚ is projective, and that Ext_C is
available in universe w. The three UCT groups are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q),
and ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)); all products range over ℤ and Q retains its differential. The
right UCT map followed by precomposition with πₚ equals the cohomology restriction Hⁿ Hom(P,Q) →
Hⁿ Hom(Z⁰(P),Q), followed by the full cycles-Hom cohomology comparison. This fixes its original
cycles representatives and degree-sign convention. -/
@[reassoc]
lemma homUniversalCoefficientSequenceEngine_right_representative (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
    (homUniversalCoefficientSequenceEngine P Q n hP hI).g ≫
        homUctHomKernelInclusion P (fun p => Q.homology (n - p)) =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCyclesSequence P Q).g n) ≫
        (homUctCyclesCohomologyIso P Q n hZ).hom := by
  let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let G := homCochainComplex (cyclesZeroComplex P) Q
  let F := homCochainComplex (outgoingImageZeroComplex P) Q
  let S : ShortComplex AddCommGrpCat.{max v w} := homCyclesCohomologyClip P Q n hI
  let T : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - p))
  let e₃ : S.X₃ ≅ T.X₃ := homUctKernelIso P Q n hI hZ
  let b : U.obj (G.homology n) ≅ A.X₁ := homUctCyclesCohomologyIso P Q n hZ
  let d : U.obj (G.homology n) ⟶ U.obj (F.homology (n + 1)) := U.map
    ((homCyclesSequence_shortExact P Q hI).δ n (n + 1) (ComplexShape.up_mk n (n + 1) rfl))
  let ι : S.X₃ ⟶ U.obj (G.homology n) := kernel.ι d
  let κ : T.X₃ ⟶ A.X₁ := homUctHomKernelInclusion P (fun p => Q.homology (n - p))
  let a : S.X₂ ⟶ U.obj (G.homology n) :=
    U.map (HomologicalComplex.homologyMap (homCyclesSequence P Q).g n)
  have hg : T.g = S.g ≫ e₃.hom := rfl
  have hκ : e₃.hom ≫ κ = ι ≫ b.hom := homUctKernelIso_hom_inclusion P Q n hI hZ
  have hClip : S.g ≫ ι = a :=
    ComposableArrows.middleKernelCokernelSequence_g_ι (homCyclesFourArrowSequence P Q n hI) _
  change T.g ≫ κ = a ≫ b.hom
  calc
    _ = (S.g ≫ e₃.hom) ≫ κ := congrArg (fun x => x ≫ κ) hg
    _ = S.g ≫ (e₃.hom ≫ κ) := Category.assoc _ _ _
    _ = S.g ≫ (ι ≫ b.hom) := congrArg (fun x => S.g ≫ x) hκ
    _ = (S.g ≫ ι) ≫ b.hom := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun x => x ≫ b.hom) hClip

/-- Let C be abelian with object universe u, morphism universe v and Ext universe w. Let f : P′ → P
be an integer chain map, g : Q → Q′ an integer cochain map, and n ∈ ℤ. Assume every term and
differential image of P and P′ is projective. The full-product UCT sequence for (P,Q) maps to
that for (P′,Q′). Its three components are, respectively, coordinatewise Ext¹
pullback/pushforward, Hⁿ Hom(f,g), and coordinatewise Hom precomposition/postcomposition, all in
the common group universe max(v,w). -/
def homUniversalCoefficientSequenceEngineMap {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    homUniversalCoefficientSequenceEngine P Q n hP hI ⟶
      homUniversalCoefficientSequenceEngine P' Q' n hP' hI' := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let E : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let E' : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P' Q' n hP' hI'
  let hZ : ∀ p : ℤ, Projective (P.cycles p) := by exact projectiveUctCycles P hP hI
  let hZ' : ∀ p : ℤ, Projective (P'.cycles p) := by exact projectiveUctCycles P' hP' hI'
  let S : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) := homCyclesSequence P Q
  let S' : ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) := homCyclesSequence P' Q'
  let φ : S ⟶ S' := homCyclesSequenceMap f g
  let m : E.X₂ ⟶ E'.X₂ := U.map (HomologicalComplex.homologyMap φ.τ₂ n)
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - 1 - p))
  let A' : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P' (fun p => Q'.homology (n - 1 - p))
  let B : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - p))
  let B' : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P' (fun p => Q'.homology (n - p))
  let L : A ⟶ A' := homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - 1 - p))
  let R : B ⟶ B' := homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - p))
  let H : E.X₃ ⟶ E'.X₃ :=
    homUctHomProductMap f (fun p => HomologicalComplex.homologyMap g (n - p))
  have hMapSquare {X Y X' Y' : CochainComplex AddCommGrpCat.{v} ℤ}
      (a : X ⟶ Y) (b : Y ⟶ Y') (c : X ⟶ X') (d : X' ⟶ Y') (h : a ≫ b = c ≫ d) :
      U.map (HomologicalComplex.homologyMap a n) ≫ U.map (HomologicalComplex.homologyMap b n) =
        U.map (HomologicalComplex.homologyMap c n) ≫
          U.map (HomologicalComplex.homologyMap d n) := by
    have hH : HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap b n =
        HomologicalComplex.homologyMap c n ≫ HomologicalComplex.homologyMap d n :=
      (HomologicalComplex.homologyMap_comp a b n).symm.trans
        ((congrArg (fun t : X ⟶ Y' => HomologicalComplex.homologyMap t n) h).trans
          (HomologicalComplex.homologyMap_comp c d n))
    exact (U.map_comp (HomologicalComplex.homologyMap a n)
      (HomologicalComplex.homologyMap b n)).symm.trans
        ((congrArg U.map hH).trans (U.map_comp (HomologicalComplex.homologyMap c n)
          (HomologicalComplex.homologyMap d n)))
  change E ⟶ E'
  refine
    { τ₁ := L.τ₃
      τ₂ := m
      τ₃ := H
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · let b : U.obj (S.X₁.homology n) ≅ A.X₂ :=
      homUctImagesCohomologyIso P Q (n - 1) n (by omega) hI
    let b' : U.obj (S'.X₁.homology n) ≅ A'.X₂ :=
      homUctImagesCohomologyIso P' Q' (n - 1) n (by omega) hI'
    let mI : U.obj (S.X₁.homology n) ⟶ U.obj (S'.X₁.homology n) :=
      U.map (HomologicalComplex.homologyMap φ.τ₁ n)
    let i : U.obj (S.X₁.homology n) ⟶ E.X₂ :=
      U.map (HomologicalComplex.homologyMap S.f n)
    let i' : U.obj (S'.X₁.homology n) ⟶ E'.X₂ :=
      U.map (HomologicalComplex.homologyMap S'.f n)
    let a : U.obj (S.X₁.homology n) ⟶ E.X₁ := b.hom ≫ A.g
    letI : Epi A.g := homUctProductPresentation_epi P _ hZ
    let bh : U.obj (S.X₁.homology n) ⟶ A.X₂ := b.hom
    let ag : A.X₂ ⟶ A.X₃ := A.g
    have hB : Epi bh := by
      change Epi b.hom
      infer_instance
    have hG : Epi ag := by
      change Epi A.g
      infer_instance
    letI : Epi a := by
      change Epi (bh ≫ ag)
      exact epi_comp' hB hG
    have hb : mI ≫ b'.hom = b.hom ≫ L.τ₂ :=
      homUctImagesCohomologyIso_naturality f g (n - 1) n (by omega) hI hI'
    have hi : i ≫ m = mI ≫ i' := hMapSquare S.f φ.τ₂ φ.τ₁ S'.f φ.comm₁₂.symm
    have hLeft : a ≫ E.f = i :=
      (Category.assoc b.hom A.g E.f).trans
        (homUniversalCoefficientSequenceEngine_left_representative P Q n hP hI)
    have hLeft' : b'.hom ≫ A'.g ≫ E'.f = i' :=
      homUniversalCoefficientSequenceEngine_left_representative P' Q' n hP' hI'
    have hL : A.g ≫ L.τ₃ = L.τ₂ ≫ A'.g := L.comm₂₃.symm
    have hAfter : A.g ≫ (L.τ₃ ≫ E'.f) = L.τ₂ ≫ (A'.g ≫ E'.f) :=
      (Category.assoc A.g L.τ₃ E'.f).symm.trans
        ((congrArg (fun t => t ≫ E'.f) hL).trans (Category.assoc L.τ₂ A'.g E'.f))
    change L.τ₃ ≫ E'.f = E.f ≫ m
    apply (cancel_epi a).1
    calc
      a ≫ (L.τ₃ ≫ E'.f) = b.hom ≫ (A.g ≫ (L.τ₃ ≫ E'.f)) := Category.assoc _ _ _
      _ = b.hom ≫ (L.τ₂ ≫ (A'.g ≫ E'.f)) := congrArg (fun t => b.hom ≫ t) hAfter
      _ = (b.hom ≫ L.τ₂) ≫ (A'.g ≫ E'.f) := (Category.assoc _ _ _).symm
      _ = (mI ≫ b'.hom) ≫ (A'.g ≫ E'.f) := congrArg (fun t => t ≫ (A'.g ≫ E'.f)) hb.symm
      _ = mI ≫ (b'.hom ≫ A'.g ≫ E'.f) := Category.assoc _ _ _
      _ = mI ≫ i' := congrArg (fun t => mI ≫ t) hLeft'
      _ = i ≫ m := hi.symm
      _ = (a ≫ E.f) ≫ m := congrArg (fun t => t ≫ m) hLeft.symm
      _ = a ≫ (E.f ≫ m) := Category.assoc _ _ _
  · let κ : E.X₃ ⟶ B.X₁ := homUctHomKernelInclusion P (fun p => Q.homology (n - p))
    let κ' : E'.X₃ ⟶ B'.X₁ := homUctHomKernelInclusion P' (fun p => Q'.homology (n - p))
    let c : U.obj (S.X₃.homology n) ≅ B.X₁ := homUctCyclesCohomologyIso P Q n hZ
    let c' : U.obj (S'.X₃.homology n) ≅ B'.X₁ := homUctCyclesCohomologyIso P' Q' n hZ'
    let mZ : U.obj (S.X₃.homology n) ⟶ U.obj (S'.X₃.homology n) :=
      U.map (HomologicalComplex.homologyMap φ.τ₃ n)
    let q : E.X₂ ⟶ U.obj (S.X₃.homology n) := U.map (HomologicalComplex.homologyMap S.g n)
    let q' : E'.X₂ ⟶ U.obj (S'.X₃.homology n) := U.map (HomologicalComplex.homologyMap S'.g n)
    letI : Mono κ' := homUctHomKernelInclusion_mono P' _
    have hc : mZ ≫ c'.hom = c.hom ≫ R.τ₁ :=
      homUctCyclesCohomologyIso_naturality f g n hZ hZ'
    have hκ : κ ≫ R.τ₁ = H ≫ κ' := homUctHomKernelInclusion_naturality f _
    have hq : m ≫ q' = q ≫ mZ := hMapSquare φ.τ₂ S'.g S.g φ.τ₃ φ.comm₂₃
    have hRight : E.g ≫ κ = q ≫ c.hom :=
      homUniversalCoefficientSequenceEngine_right_representative P Q n hP hI
    have hRight' : E'.g ≫ κ' = q' ≫ c'.hom :=
      homUniversalCoefficientSequenceEngine_right_representative P' Q' n hP' hI'
    change m ≫ E'.g = E.g ≫ H
    apply (cancel_mono κ').1
    calc
      (m ≫ E'.g) ≫ κ' = m ≫ (E'.g ≫ κ') := Category.assoc _ _ _
      _ = m ≫ (q' ≫ c'.hom) := congrArg (fun t => m ≫ t) hRight'
      _ = (m ≫ q') ≫ c'.hom := (Category.assoc _ _ _).symm
      _ = (q ≫ mZ) ≫ c'.hom := congrArg (fun t => t ≫ c'.hom) hq
      _ = q ≫ (mZ ≫ c'.hom) := Category.assoc _ _ _
      _ = q ≫ (c.hom ≫ R.τ₁) := congrArg (fun t => q ≫ t) hc
      _ = (q ≫ c.hom) ≫ R.τ₁ := (Category.assoc _ _ _).symm
      _ = (E.g ≫ κ) ≫ R.τ₁ := congrArg (fun t => t ≫ R.τ₁) hRight.symm
      _ = E.g ≫ (κ ≫ R.τ₁) := Category.assoc _ _ _
      _ = E.g ≫ (H ≫ κ') := congrArg (fun t => E.g ≫ t) hκ
      _ = (E.g ≫ H) ≫ κ' := (Category.assoc _ _ _).symm

/-- Let C be abelian with object universe u, morphism universe v and Ext universe w. Let f : P′ → P
be an integer chain map, g : Q → Q′ an integer cochain map, and n ∈ ℤ. Assume every term and
differential image of P and P′ is projective. The middle UCT component is precisely Hⁿ Hom(f,g),
preserving the original full Hom differential and its common-universe cohomology object. -/
lemma homUniversalCoefficientSequenceEngineMap_τ₂ {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI').τ₂ =
      AddCommGrpCat.uliftFunctor.{w, v}.map
        (HomologicalComplex.homologyMap (homCochainComplexMap f g) n) := by
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let E : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let E' : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P' Q' n hP' hI'
  let M : E ⟶ E' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let φ : homCyclesSequence P Q ⟶ homCyclesSequence P' Q' := homCyclesSequenceMap f g
  have hPack : M.τ₂ = U.map (HomologicalComplex.homologyMap φ.τ₂ n) := rfl
  have hφ : φ.τ₂ = homCochainComplexMap f g := homCyclesSequenceMap_τ₂ f g
  change M.τ₂ = U.map (HomologicalComplex.homologyMap (homCochainComplexMap f g) n)
  exact hPack.trans
    (congrArg (fun t : homCochainComplex P Q ⟶ homCochainComplex P' Q' =>
      U.map (HomologicalComplex.homologyMap t n)) hφ)

/-- Let C be abelian with object universe u, morphism universe v and Ext universe w. Let f : P′ → P
be an integer chain map, g : Q → Q′ an integer cochain map, and n ∈ ℤ. Assume every term and
differential image of P and P′ is projective. On the full left product, eₚ ∈
Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) is sent to (H^{n-1-p}(g))_*(Hₚ(f))^* eₚ, using the actual Yoneda
degree-zero compositions. -/
lemma homUniversalCoefficientSequenceEngineMap_τ₁_apply {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1))))
    (e : (homUniversalCoefficientSequenceEngine P Q n hP hI).X₁) (p : ℤ) :
    (homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI').τ₁ e p =
      ULift.up (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e p).down
        (zero_add 1)).comp
        (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)) := by
  let E : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let E' : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P' Q' n hP' hI'
  let A : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P (fun p => Q.homology (n - 1 - p))
  let A' : ShortComplex AddCommGrpCat.{max v w} :=
    homUctProductPresentation P' (fun p => Q'.homology (n - 1 - p))
  let L : A ⟶ A' := homUctProductPresentationMap f
    (fun p => HomologicalComplex.homologyMap g (n - 1 - p))
  let M : E ⟶ E' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let e₀ : ∀ p : ℤ, ULift.{v, w}
      (Ext.{w} (P.homology p) (Q.homology (n - 1 - p)) 1) := e
  have hPack : M.τ₁ = L.τ₃ := rfl
  have hApply : M.τ₁.hom e₀ p = L.τ₃.hom e₀ p :=
    congrArg (fun t : E.X₁ ⟶ E'.X₁ => t.hom e₀ p) hPack
  have hValue : L.τ₃.hom e₀ p =
      ULift.up (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e₀ p).down
        (zero_add 1)).comp
        (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)) :=
    homUctProductPresentationMap_τ₃_apply f
      (fun p => HomologicalComplex.homologyMap g (n - 1 - p)) e₀ p
  change M.τ₁.hom e₀ p = _
  exact hApply.trans hValue

/-- Let C be abelian with object universe u, morphism universe v and Ext universe w. Let f : P′ → P
be an integer chain map, g : Q → Q′ an integer cochain map, and n ∈ ℤ. Assume every term and
differential image of P and P′ is projective. On the full right product, tₚ : Hₚ(P) → H^{n-p}(Q)
is sent to H^{n-p}(g) ∘ tₚ ∘ Hₚ(f) in each integer degree. -/
lemma homUniversalCoefficientSequenceEngineMap_τ₃_apply {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1))))
    (k : (homUniversalCoefficientSequenceEngine P Q n hP hI).X₃) (p : ℤ) :
    (homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI').τ₃ k p =
      ULift.up (HomologicalComplex.homologyMap f p ≫ (k p).down ≫
        HomologicalComplex.homologyMap g (n - p)) := by
  let E : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P Q n hP hI
  let E' : ShortComplex AddCommGrpCat.{max v w} :=
    homUniversalCoefficientSequenceEngine P' Q' n hP' hI'
  let H : E.X₃ ⟶ E'.X₃ :=
    homUctHomProductMap f (fun p => HomologicalComplex.homologyMap g (n - p))
  let M : E ⟶ E' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let k₀ : ∀ p : ℤ, ULift.{w, v} (P.homology p ⟶ Q.homology (n - p)) := k
  have hPack : M.τ₃ = H := rfl
  have hApply : M.τ₃.hom k₀ p = H.hom k₀ p :=
    congrArg (fun t : E.X₃ ⟶ E'.X₃ => t.hom k₀ p) hPack
  have hValue : H.hom k₀ p = ULift.up
      (HomologicalComplex.homologyMap f p ≫ (k₀ p).down ≫
        HomologicalComplex.homologyMap g (n - p)) := rfl
  change M.τ₃.hom k₀ p = _
  exact hApply.trans hValue

end Endpoints

section Standard

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Using the standard Ext groups in
universe max(u,v), the three common-universe comparisons identify the lifted full Ext¹ product
with ∏ₚ Ext¹(Hₚ(P),H^{n-1-p}(Q)), identify the two lifts of Hⁿ Hom(P,Q), and identify the
product of lifted Hom groups with the lift of ∏ₚ Hom(Hₚ(P),H^{n-p}(Q)). These comparisons
require no projectivity and change no morphism representatives. -/
def homUniversalCoefficientStandardCoordinates
    (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ) :
    letI := HasExt.standard C
    (AddCommGrpCat.of
        (∀ p : ℤ, ULift.{v, max u v}
          (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ≅
      AddCommGrpCat.of
        (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ×
      ((AddCommGrpCat.uliftFunctor.{max u v, v}.obj
          ((homCochainComplex P Q).homology n) ≅
        AddCommGrpCat.uliftFunctor.{u, v}.obj ((homCochainComplex P Q).homology n)) ×
        (AddCommGrpCat.of
            (∀ p : ℤ, ULift.{max u v, v} (P.homology p ⟶ Q.homology (n - p))) ≅
          AddCommGrpCat.uliftFunctor.{u, v}.obj
            (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p))))) := by
  letI := HasExt.standard C
  let H := (homCochainComplex P Q).homology n
  let A := fun p : ℤ => AddCommGrpCat.of (P.homology p ⟶ Q.homology (n - p))
  let e₁ : AddCommGrpCat.of
      (∀ p : ℤ, ULift.{v, max u v}
        (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ≅
      AddCommGrpCat.of
        (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1) :=
    (AddEquiv.piCongrRight fun p =>
      (AddEquiv.ulift : ULift.{v, max u v}
        (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1) ≃+
        Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)).toAddCommGrpIso
  let e₂ : AddCommGrpCat.uliftFunctor.{max u v, v}.obj H ≅
      AddCommGrpCat.uliftFunctor.{u, v}.obj H :=
    ((AddEquiv.ulift : ULift.{max u v, v} H ≃+ H).trans
      (AddEquiv.ulift : ULift.{u, v} H ≃+ H).symm).toAddCommGrpIso
  let PiA := ∀ p : ℤ, A p
  let relift : ULift.{max u v, v} PiA ≃+ ULift.{u, v} PiA :=
    (AddEquiv.ulift : ULift.{max u v, v} PiA ≃+ PiA).trans
      (AddEquiv.ulift : ULift.{u, v} PiA ≃+ PiA).symm
  let e₃ : AddCommGrpCat.of (∀ p : ℤ, ULift.{max u v, v} (A p)) ≅
      AddCommGrpCat.uliftFunctor.{u, v}.obj (AddCommGrpCat.of (∀ p : ℤ, A p)) :=
    (AddCommGrpCat.uliftIntPiIso.{v, max u v} A).symm ≪≫ relift.toAddCommGrpIso
  exact (e₁, e₂, e₃)

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. These groups
form the full-product UCT short complex. The first arrow is positive Yoneda normalization
followed by the Hom cohomology inclusion, and the second is cycles restriction followed by
homology descent. All products run over every integer degree. -/
def homUniversalCoefficientSequence (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    ShortComplex AddCommGrpCat.{max u v} := by
  letI := HasExt.standard C
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let X₁ : AddCommGrpCat.{max u v} := AddCommGrpCat.of
    (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)
  let X₂ : AddCommGrpCat.{max u v} :=
    AddCommGrpCat.uliftFunctor.{u, v}.obj ((homCochainComplex P Q).homology n)
  let X₃ : AddCommGrpCat.{max u v} := AddCommGrpCat.uliftFunctor.{u, v}.obj
    (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p)))
  let e := homUniversalCoefficientStandardCoordinates P Q n
  let e₁ : S.X₁ ≅ X₁ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{v, max u v}
        (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ≅ X₁
    exact e.1
  let e₂ : S.X₂ ≅ X₂ := by
    change AddCommGrpCat.uliftFunctor.{max u v, v}.obj
      ((homCochainComplex P Q).homology n) ≅ X₂
    exact e.2.1
  let e₃ : S.X₃ ≅ X₃ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{max u v, v} (P.homology p ⟶ Q.homology (n - p))) ≅ X₃
    exact e.2.2
  exact S.changeObjects e₁ e₂ e₃

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. The standard
left object is the unlifted full product ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), whose Ext groups already
lie in universe max(u,v). -/
lemma homUniversalCoefficientSequence_X₁ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    letI := HasExt.standard C
    (homUniversalCoefficientSequence P Q n hP hI).X₁ = AddCommGrpCat.of
      (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. The standard
middle object is the canonical common-universe lift of Hⁿ Hom(P,Q), with the full Hom
differential retained. -/
lemma homUniversalCoefficientSequence_X₂ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequence P Q n hP hI).X₂ =
      AddCommGrpCat.uliftFunctor.{u, v}.obj ((homCochainComplex P Q).homology n) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. The standard
right object is the canonical common-universe lift of ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), over all
integers p. -/
lemma homUniversalCoefficientSequence_X₃ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequence P Q n hP hI).X₃ =
      AddCommGrpCat.uliftFunctor.{u, v}.obj
        (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p))) := rfl

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. Changing to
the standard common-universe coordinates gives an isomorphism of short complexes from the
full-product UCT constructed with Ext universe max(u,v) to the standard UCT sequence. Every
component preserves the underlying Ext, cohomology and Hom representatives. -/
def homUniversalCoefficientSequenceIso (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    letI := HasExt.standard C
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI ≅
      homUniversalCoefficientSequence P Q n hP hI := by
  letI := HasExt.standard C
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let X₁ : AddCommGrpCat.{max u v} := AddCommGrpCat.of
    (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)
  let X₂ : AddCommGrpCat.{max u v} :=
    AddCommGrpCat.uliftFunctor.{u, v}.obj ((homCochainComplex P Q).homology n)
  let X₃ : AddCommGrpCat.{max u v} := AddCommGrpCat.uliftFunctor.{u, v}.obj
    (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p)))
  let e := homUniversalCoefficientStandardCoordinates P Q n
  let e₁ : S.X₁ ≅ X₁ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{v, max u v}
        (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ≅ X₁
    exact e.1
  let e₂ : S.X₂ ≅ X₂ := by
    change AddCommGrpCat.uliftFunctor.{max u v, v}.obj
      ((homCochainComplex P Q).homology n) ≅ X₂
    exact e.2.1
  let e₃ : S.X₃ ≅ X₃ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{max u v, v} (P.homology p ⟶ Q.homology (n - p))) ≅ X₃
    exact e.2.2
  change S ≅ S.changeObjects e₁ e₂ e₃
  exact S.changeObjectsIso e₁ e₂ e₃

/-- Let C be an abelian category with object universe u and morphism universe v. Let P be an integer
chain complex, Q an integer cochain complex, and n an integer. Let I⁰(P) and Z⁰(P) be the
outgoing-image and cycles complexes with zero differential. Assume all differential images
im(d_P : Pₚ → Pₚ₋₁) are projective. Assume also every Pₚ is projective. Take the standard Ext
groups in universe max(u,v). The UCT terms are ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)), Hⁿ Hom(P,Q), and
∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)), with their canonical common-universe identifications. The sequence 0
→ ∏ₚ Ext¹_C(Hₚ(P),H^{n-1-p}(Q)) → Hⁿ Hom(P,Q) → ∏ₚ Hom_C(Hₚ(P),H^{n-p}(Q)) → 0 is short exact.
The left product uses standard Ext classes, while the middle and full right product are
canonically lifted to universe max(u,v). The maps are the positive Hom-sequence inclusion and
canonical cycles restriction, after the Ext and Hom endpoint comparisons. Q has its original
differential. -/
lemma homUniversalCoefficientSequence_shortExact (P : ChainComplex C ℤ)
    (Q : CochainComplex C ℤ) (n : ℤ) (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1)))) :
    (homUniversalCoefficientSequence P Q n hP hI).ShortExact := by
  letI := HasExt.standard C
  exact ShortComplex.shortExact_of_iso (homUniversalCoefficientSequenceIso P Q n hP hI)
    (homUniversalCoefficientSequenceEngine_shortExact P Q n hP hI)

/-- Let C be abelian with object universe u, morphism universe v and the standard Ext groups in
universe max(u,v). Let f : P′ → P be an integer chain map, g : Q → Q′ an integer cochain map,
and n ∈ ℤ. Assume every term and differential image of P and P′ is projective. The standard
full-product UCT sequence maps from (P,Q) to (P′,Q′). Its left map is coordinatewise Yoneda Ext¹
action, its middle map is Hⁿ Hom(f,g), and its right map is the full homology Hom action. -/
def homUniversalCoefficientSequenceMap {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    homUniversalCoefficientSequence P Q n hP hI ⟶
      homUniversalCoefficientSequence P' Q' n hP' hI' := by
  letI := HasExt.standard C
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let S' : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P' Q' n hP' hI'
  let T : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P Q n hP hI
  let T' : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P' Q' n hP' hI'
  let e : S ≅ T := homUniversalCoefficientSequenceIso P Q n hP hI
  let e' : S' ≅ T' := homUniversalCoefficientSequenceIso P' Q' n hP' hI'
  let m : S ⟶ S' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  change T ⟶ T'
  exact e.inv ≫ m ≫ e'.hom

/-- Let C be abelian with object universe u, morphism universe v and the standard Ext groups in
universe max(u,v). Let f : P′ → P be an integer chain map, g : Q → Q′ an integer cochain map,
and n ∈ ℤ. Assume every term and differential image of P and P′ is projective. The middle
component is the canonical common-universe lift of Hⁿ Hom(f,g), with the original full Hom
cochain map. -/
lemma homUniversalCoefficientSequenceMap_τ₂ {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1)))) :
    (homUniversalCoefficientSequenceMap f g n hP hI hP' hI').τ₂ =
      AddCommGrpCat.uliftFunctor.{u, v}.map
        (HomologicalComplex.homologyMap (homCochainComplexMap f g) n) := by
  letI := HasExt.standard C
  let U := AddCommGrpCat.uliftFunctor.{max u v, v}
  let V := AddCommGrpCat.uliftFunctor.{u, v}
  let H : AddCommGrpCat.{v} := (homCochainComplex P Q).homology n
  let H' : AddCommGrpCat.{v} := (homCochainComplex P' Q').homology n
  let α : H ⟶ H' := HomologicalComplex.homologyMap (homCochainComplexMap f g) n
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let S' : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P' Q' n hP' hI'
  let T : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P Q n hP hI
  let T' : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P' Q' n hP' hI'
  let m : S ⟶ S' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let M : T ⟶ T' := homUniversalCoefficientSequenceMap f g n hP hI hP' hI'
  let c : S.X₂ ≅ T.X₂ := by
    change U.obj H ≅ V.obj H
    exact (homUniversalCoefficientStandardCoordinates P Q n).2.1
  let c' : S'.X₂ ≅ T'.X₂ := by
    change U.obj H' ≅ V.obj H'
    exact (homUniversalCoefficientStandardCoordinates P' Q' n).2.1
  have hPack : M.τ₂ = c.inv ≫ m.τ₂ ≫ c'.hom := rfl
  have hm : m.τ₂ = U.map α := homUniversalCoefficientSequenceEngineMap_τ₂ f g n hP hI hP' hI'
  have hField : M.τ₂ = c.inv ≫ U.map α ≫ c'.hom :=
    hPack.trans (congrArg (fun a : S.X₂ ⟶ S'.X₂ => c.inv ≫ a ≫ c'.hom) hm)
  change M.τ₂ = V.map α
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  let z₀ : ULift.{u, v} H := z
  let z₁ : ULift.{max u v, v} H := c.inv.hom z₀
  let z₂ : ULift.{max u v, v} H' := (U.map α).hom z₁
  have h₁ : z₁ = ULift.up z₀.down := rfl
  have h₂ : z₂ = ULift.up (α.hom z₁.down) := rfl
  have h₃ : c'.hom.hom z₂ = ULift.up z₂.down := rfl
  have hDown : z₂.down = α.hom z₀.down :=
    (congrArg (fun x : ULift.{max u v, v} H' => x.down) h₂).trans
      (congrArg α.hom (congrArg (fun x : ULift.{max u v, v} H => x.down) h₁))
  have hComposite : (c.inv ≫ U.map α ≫ c'.hom).hom z₀ = c'.hom.hom z₂ :=
    (AddCommGrpCat.comp_apply c.inv (U.map α ≫ c'.hom) z₀).trans
      (AddCommGrpCat.comp_apply (U.map α) c'.hom z₁)
  have hTarget : (V.map α).hom z₀ = ULift.up (α.hom z₀.down) := rfl
  exact (congrArg (fun a : T.X₂ ⟶ T'.X₂ => a.hom z₀) hField).trans
    (hComposite.trans (h₃.trans ((congrArg ULift.up hDown).trans hTarget.symm)))

/-- Let C be abelian with object universe u, morphism universe v and the standard Ext groups in
universe max(u,v). Let f : P′ → P be an integer chain map, g : Q → Q′ an integer cochain map,
and n ∈ ℤ. Assume every term and differential image of P and P′ is projective. For each integer
p, the left product component sends eₚ to its pullback along Hₚ(f), followed by pushforward
along H^{n-1-p}(g), in Ext¹_C(Hₚ(P′),H^{n-1-p}(Q′)). -/
lemma homUniversalCoefficientSequenceMap_τ₁_apply {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1))))
    (e : (homUniversalCoefficientSequence P Q n hP hI).X₁) (p : ℤ) :
    letI := HasExt.standard C
    (homUniversalCoefficientSequenceMap f g n hP hI hP' hI').τ₁ e p =
      ((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e p) (zero_add 1)).comp
        (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1) := by
  letI := HasExt.standard C
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let S' : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P' Q' n hP' hI'
  let T : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P Q n hP hI
  let T' : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P' Q' n hP' hI'
  let m : S ⟶ S' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let M : T ⟶ T' := homUniversalCoefficientSequenceMap f g n hP hI hP' hI'
  let c : S.X₁ ≅ T.X₁ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{v, max u v}
        (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)) ≅ AddCommGrpCat.of
          (∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1)
    exact (homUniversalCoefficientStandardCoordinates P Q n).1
  let c' : S'.X₁ ≅ T'.X₁ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{v, max u v}
        (Ext.{max u v} (P'.homology p) (Q'.homology (n - 1 - p)) 1)) ≅ AddCommGrpCat.of
          (∀ p : ℤ, Ext.{max u v} (P'.homology p) (Q'.homology (n - 1 - p)) 1)
    exact (homUniversalCoefficientStandardCoordinates P' Q' n).1
  let e₀ : ∀ p : ℤ, Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1 := e
  let e₁ : ∀ p : ℤ, ULift.{v, max u v}
      (Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1) := c.inv.hom e₀
  let e₂ : ∀ p : ℤ, ULift.{v, max u v}
      (Ext.{max u v} (P'.homology p) (Q'.homology (n - 1 - p)) 1) := m.τ₁.hom e₁
  let a : Ext.{max u v} (P'.homology p) (Q'.homology (n - 1 - p)) 1 :=
    ((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e₀ p) (zero_add 1)).comp
      (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)
  have hPack : M.τ₁ = c.inv ≫ m.τ₁ ≫ c'.hom := rfl
  have h₁ : (e₁ p).down = e₀ p := rfl
  have h₂ : e₂ p = ULift.up
      (((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp (e₁ p).down (zero_add 1)).comp
        (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)) :=
    homUniversalCoefficientSequenceEngineMap_τ₁_apply f g n hP hI hP' hI' e₁ p
  have h₃ : c'.hom.hom e₂ p = (e₂ p).down := rfl
  have hDown : (e₂ p).down = a :=
    (congrArg (fun x : ULift.{v, max u v}
      (Ext.{max u v} (P'.homology p) (Q'.homology (n - 1 - p)) 1) => x.down) h₂).trans
        (congrArg (fun x : Ext.{max u v} (P.homology p) (Q.homology (n - 1 - p)) 1 =>
          ((Ext.mk₀ (HomologicalComplex.homologyMap f p)).comp x (zero_add 1)).comp
            (Ext.mk₀ (HomologicalComplex.homologyMap g (n - 1 - p))) (add_zero 1)) h₁)
  have hComposite : (c.inv ≫ m.τ₁ ≫ c'.hom).hom e₀ = c'.hom.hom e₂ :=
    (AddCommGrpCat.comp_apply c.inv (m.τ₁ ≫ c'.hom) e₀).trans
      (AddCommGrpCat.comp_apply m.τ₁ c'.hom e₁)
  have hApply : M.τ₁.hom e₀ p = c'.hom.hom e₂ p :=
    (congrArg (fun a : T.X₁ ⟶ T'.X₁ => a.hom e₀ p) hPack).trans
      (congrArg (fun x : T'.X₁ => x p) hComposite)
  change M.τ₁.hom e₀ p = a
  exact hApply.trans (h₃.trans hDown)

/-- Let C be abelian with object universe u, morphism universe v and the standard Ext groups in
universe max(u,v). Let f : P′ → P be an integer chain map, g : Q → Q′ an integer cochain map,
and n ∈ ℤ. Assume every term and differential image of P and P′ is projective. For each integer
p, the right product component sends tₚ to H^{n-p}(g) ∘ tₚ ∘ Hₚ(f), with the canonical lift of
the entire Hom family. -/
lemma homUniversalCoefficientSequenceMap_τ₃_apply {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (hP : ∀ p : ℤ, Projective (P.X p))
    (hI : ∀ p, Projective (Abelian.image (P.d p (p - 1))))
    (hP' : ∀ p : ℤ, Projective (P'.X p))
    (hI' : ∀ p, Projective (Abelian.image (P'.d p (p - 1))))
    (k : (homUniversalCoefficientSequence P Q n hP hI).X₃) :
    (homUniversalCoefficientSequenceMap f g n hP hI hP' hI').τ₃ k =
      ULift.up (fun p : ℤ => HomologicalComplex.homologyMap f p ≫ k.down p ≫
        HomologicalComplex.homologyMap g (n - p)) := by
  letI := HasExt.standard C
  let S : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P Q n hP hI
  let S' : ShortComplex AddCommGrpCat.{max u v} :=
    homUniversalCoefficientSequenceEngine.{u, v, max u v} P' Q' n hP' hI'
  let T : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P Q n hP hI
  let T' : ShortComplex AddCommGrpCat.{max u v} := homUniversalCoefficientSequence P' Q' n hP' hI'
  let m : S ⟶ S' := homUniversalCoefficientSequenceEngineMap f g n hP hI hP' hI'
  let M : T ⟶ T' := homUniversalCoefficientSequenceMap f g n hP hI hP' hI'
  let c : S.X₃ ≅ T.X₃ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{max u v, v} (P.homology p ⟶ Q.homology (n - p))) ≅
        AddCommGrpCat.uliftFunctor.{u, v}.obj
          (AddCommGrpCat.of (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p)))
    exact (homUniversalCoefficientStandardCoordinates P Q n).2.2
  let c' : S'.X₃ ≅ T'.X₃ := by
    change AddCommGrpCat.of
      (∀ p : ℤ, ULift.{max u v, v} (P'.homology p ⟶ Q'.homology (n - p))) ≅
        AddCommGrpCat.uliftFunctor.{u, v}.obj
          (AddCommGrpCat.of (∀ p : ℤ, P'.homology p ⟶ Q'.homology (n - p)))
    exact (homUniversalCoefficientStandardCoordinates P' Q' n).2.2
  let k₀ : ULift.{u, v} (∀ p : ℤ, P.homology p ⟶ Q.homology (n - p)) := k
  let k₁ : ∀ p : ℤ, ULift.{max u v, v} (P.homology p ⟶ Q.homology (n - p)) :=
    c.inv.hom k₀
  let k₂ : ∀ p : ℤ, ULift.{max u v, v} (P'.homology p ⟶ Q'.homology (n - p)) :=
    m.τ₃.hom k₁
  have hPack : M.τ₃ = c.inv ≫ m.τ₃ ≫ c'.hom := rfl
  have h₁ (p : ℤ) : (k₁ p).down = k₀.down p := rfl
  have h₂ (p : ℤ) : k₂ p = ULift.up
      (HomologicalComplex.homologyMap f p ≫ (k₁ p).down ≫
        HomologicalComplex.homologyMap g (n - p)) :=
    homUniversalCoefficientSequenceEngineMap_τ₃_apply f g n hP hI hP' hI' k₁ p
  have h₃ : c'.hom.hom k₂ = ULift.up (fun p : ℤ => (k₂ p).down) := rfl
  have hDown (p : ℤ) : (k₂ p).down = HomologicalComplex.homologyMap f p ≫ k₀.down p ≫
      HomologicalComplex.homologyMap g (n - p) :=
    (congrArg (fun x : ULift.{max u v, v}
      (P'.homology p ⟶ Q'.homology (n - p)) => x.down) (h₂ p)).trans
        (congrArg (fun x : P.homology p ⟶ Q.homology (n - p) =>
          HomologicalComplex.homologyMap f p ≫ x ≫ HomologicalComplex.homologyMap g (n - p))
            (h₁ p))
  have hComposite : (c.inv ≫ m.τ₃ ≫ c'.hom).hom k₀ = c'.hom.hom k₂ :=
    (AddCommGrpCat.comp_apply c.inv (m.τ₃ ≫ c'.hom) k₀).trans
      (AddCommGrpCat.comp_apply m.τ₃ c'.hom k₁)
  change M.τ₃.hom k₀ = ULift.up (fun p : ℤ =>
    HomologicalComplex.homologyMap f p ≫ k₀.down p ≫ HomologicalComplex.homologyMap g (n - p))
  exact (congrArg (fun a : T.X₃ ⟶ T'.X₃ => a.hom k₀) hPack).trans
    (hComposite.trans (h₃.trans (congrArg ULift.up (funext hDown))))

end Standard

end ChainComplex
