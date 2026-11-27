/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Types.End
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import MathlibExt.CategoryTheory.Presentable.HomPowerAccessibility

/-!
# Original ordinary diagram presentability

The bounded Type-functor limit theorem is reused on actual cones.
The native multicospan arrow type keeps all four original constructor
families; its bound is derived from the actual left and right labels.
These are prerequisites for the original natural-transformation cone.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM uD vD uK vK t uL uR

namespace CategoryTheory.Presentable.FunctorPresentability

open Limits Opposite

/-- The original native multicospan arrows have exactly four tagged constructor families. -/
def multicospanArrowEquiv (S : MulticospanShape.{uL, uR}) :
    Arrow (WalkingMulticospan S) ≃ S.L ⊕ (S.R ⊕ (S.R ⊕ S.R)) where
  toFun a := by
    rcases a with ⟨X, Y, f⟩
    cases f with
    | id X =>
      cases X with
      | left l => exact .inl l
      | right r => exact .inr (.inl r)
    | fst r => exact .inr (.inr (.inl r))
    | snd r => exact .inr (.inr (.inr r))
  invFun a := match a with
    | .inl l => Arrow.mk (WalkingMulticospan.Hom.id (.left l))
    | .inr (.inl r) => Arrow.mk (WalkingMulticospan.Hom.id (.right r))
    | .inr (.inr (.inl r)) => Arrow.mk (WalkingMulticospan.Hom.fst r)
    | .inr (.inr (.inr r)) => Arrow.mk (WalkingMulticospan.Hom.snd r)
  left_inv a := by
    rcases a with ⟨X, Y, f⟩
    cases f with
    | id X => cases X <;> rfl
    | fst r => rfl
    | snd r => rfl
  right_inv a := by
    rcases a with l | (r | (r | r)) <;> rfl

/-- The complete first tag retains the original left-object identity. -/
theorem multicospanArrowEquiv_id_left (S : MulticospanShape.{uL, uR}) (l : S.L) :
    multicospanArrowEquiv S (Arrow.mk (𝟙 (WalkingMulticospan.left l))) = Sum.inl l := rfl

/-- The complete second tag retains the original right-object identity. -/
theorem multicospanArrowEquiv_id_right (S : MulticospanShape.{uL, uR}) (r : S.R) :
    multicospanArrowEquiv S (Arrow.mk (𝟙 (WalkingMulticospan.right r))) =
      Sum.inr (Sum.inl r) := rfl

/-- The first leg retains the native right label, even when its two endpoints coincide. -/
theorem multicospanArrowEquiv_fst (S : MulticospanShape.{uL, uR}) (r : S.R) :
    multicospanArrowEquiv S (Arrow.mk (WalkingMulticospan.Hom.fst r)) =
      Sum.inr (Sum.inr (Sum.inl r)) := rfl

/-- The second leg remains a distinct tag with the SAME original right label. -/
theorem multicospanArrowEquiv_snd (S : MulticospanShape.{uL, uR}) (r : S.R) :
    multicospanArrowEquiv S (Arrow.mk (WalkingMulticospan.Hom.snd r)) =
      Sum.inr (Sum.inr (Sum.inr r)) := rfl

/-- Actual native label bounds imply a bound on the complete native arrow type. -/
theorem multicospanArrow_bound (S : MulticospanShape.{uL, uR}) (χ : Cardinal.{w})
    (hχ : Cardinal.aleph0 ≤ χ) (hL : HasCardinalLT S.L χ) (hR : HasCardinalLT S.R χ) :
    HasCardinalLT (Arrow (WalkingMulticospan S)) χ := by
  apply (hasCardinalLT_iff_of_equiv (multicospanArrowEquiv S) χ).2
  apply (hasCardinalLT_sum_iff _ _ χ hχ).2
  refine ⟨hL, ?_⟩
  apply (hasCardinalLT_sum_iff _ _ χ hχ).2
  refine ⟨hR, ?_⟩
  exact (hasCardinalLT_sum_iff _ _ χ hχ).2 ⟨hR, hR⟩

/-- The end shape is bounded from the ORIGINAL representative arrow type.
The object bound uses its literal identity-arrow injection. -/
theorem endShapeArrow_bound {S : Type uD} [Category.{vD} S]
    (χ : Cardinal.{w}) [Fact χ.IsRegular] (hS : HasCardinalLT (Arrow S) χ) :
    HasCardinalLT (Arrow (WalkingMulticospan (multicospanShapeEnd S))) χ :=
  multicospanArrow_bound _ χ (Cardinal.IsRegular.aleph0_le Fact.out)
    (hS.of_injective (fun s : S ↦ Arrow.mk (𝟙 s))
      (fun _ _ h ↦ congr($(h).left))) hS



section SmallDiagrams

variable (M : Type uM) [Category.{vM} M] {S : Type w} [SmallCategory S] (F : S ⥤ M)

/-- The actual original Hom equations form the native end multicospan in the
Type-valued functor category. Its two maps retain post- and precomposition. -/
def equationIndex :
    MulticospanIndex (multicospanShapeEnd S) ((S ⥤ M) ⥤ Type max w vM) where
  left s := (evaluation S M).obj s ⋙ uliftCoyoneda.{w}.obj (op (F.obj s))
  right f := (evaluation S M).obj f.right ⋙ uliftCoyoneda.{w}.obj (op (F.obj f.left))
  fst f :=
    { app G := ↾fun h ↦ ULift.up (h.down ≫ G.map f.hom)
      naturality := by
        intro G H a
        ext h
        let t : F.obj f.left ⟶ G.obj f.left := h.down
        change ULift.up ((t ≫ a.app f.left) ≫ H.map f.hom) =
          ULift.up ((t ≫ G.map f.hom) ≫ a.app f.right)
        congr 1
        have ha : G.map f.hom ≫ a.app f.right = a.app f.left ≫ H.map f.hom :=
          a.naturality f.hom
        rw [Category.assoc, Category.assoc, ha] }
  snd f :=
    { app G := ↾fun h ↦ ULift.up (F.map f.hom ≫ h.down)
      naturality := by
        intro G H a
        ext h
        change ULift.up (F.map f.hom ≫ (h.down ≫ a.app f.right)) =
          ULift.up ((F.map f.hom ≫ h.down) ≫ a.app f.right)
        congr 1
        exact (Category.assoc _ _ _).symm }

/-- The actual projection is the ORIGINAL component function, with its auxiliary lift. -/
def componentProjection (s : S) :
    coyoneda.obj (op F) ⟶ (equationIndex M F).left s where
  app G := ↾fun a ↦ ULift.up (a.app s)
  naturality := by
    intro G H a
    ext f
    rfl

/-- Every original natural transformation supplies the actual component equation cone. -/
def componentCone : Multifork (equationIndex M F) :=
  Multifork.ofι _ (coyoneda.obj (op F)) (componentProjection M F) (by
    intro f
    ext G a
    change ULift.up (a.app f.left ≫ G.map f.hom) =
      ULift.up (F.map f.hom ≫ a.app f.right)
    congr 1
    exact (a.naturality f.hom).symm)

/-- The complete original projection function keeps every original component. -/
theorem componentCone_ι_app (G : S ⥤ M) (s : S) (a : F ⟶ G) :
    ((componentCone M F).ι s).app G a = ULift.up (a.app s) := rfl

/-- The right projection has the actual postcomposition function from its original left label. -/
theorem componentCone_right_app (G : S ⥤ M) (f : Arrow S) (a : F ⟶ G) :
    ((componentCone M F).π.app (.right f)).app G a =
      ULift.up (a.app f.left ≫ G.map f.hom) := rfl

/-- The whole inverse universal function reconstructs ORIGINAL natural transformations.
Its naturality uses the actual cone equation, rather than a supplied desired law. -/
def componentLift (T : Multifork (equationIndex M F)) :
    T.pt ⟶ (componentCone M F).pt where
  app G := ↾fun x ↦
    { app s := (((T.ι s).app G) x).down
      naturality := by
        intro s t f
        have h := NatTrans.congr_app (T.condition (Arrow.mk f)) G
        have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
        exact hx.symm }
  naturality := by
    intro G H a
    apply ConcreteCategory.hom_ext
    intro x
    apply NatTrans.ext
    funext s
    have h := (T.ι s).naturality a
    have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
    exact hx

/-- The reconstructed universal function has each original component value. -/
theorem componentLift_app (T : Multifork (equationIndex M F)) (G : S ⥤ M)
    (x : T.pt.obj G) (s : S) :
    ((componentLift M F T).app G x).app s = (((T.ι s).app G) x).down := rfl

/-- The actual original Hom functor is the limit of its native component equations. -/
def componentConeIsLimit : IsLimit (componentCone M F) :=
  Multifork.IsLimit.mk _ (componentLift M F)
    (by
      intro T s
      ext G x
      change ULift.up ((((T.ι s).app G) x).down) = ((T.ι s).app G) x
      exact ULift.up_down _)
    (by
      intro T m hm
      apply NatTrans.ext
      funext G
      apply ConcreteCategory.hom_ext
      intro x
      apply NatTrans.ext
      funext s
      have h := NatTrans.congr_app (hm s) G
      have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
      exact hx)

/-- The native universal lift is the whole original reconstruction function. -/
theorem componentConeIsLimit_lift (T : Multifork (equationIndex M F)) :
    (componentConeIsLimit M F).lift T = componentLift M F T := rfl

/-- Every original component projection is satisfied by the selected universal map. -/
theorem componentLift_ι (T : Multifork (equationIndex M F)) (s : S) :
    componentLift M F T ≫ (componentCone M F).ι s = T.ι s :=
  (componentConeIsLimit M F).fac T (.left s)

/-- A compatible universal map is unique on ALL original components. -/
theorem componentLift_unique (T : Multifork (equationIndex M F))
    (m : T.pt ⟶ (componentCone M F).pt)
    (hm : ∀ s : S, m ≫ (componentCone M F).ι s = T.ι s) :
    m = componentLift M F T := by
  apply Multifork.IsLimit.hom_ext (componentConeIsLimit M F)
  intro s
  exact (hm s).trans (componentLift_ι M F T s).symm

/-- Bounded native Type limits prove compactness of the SAME small-side original diagram.
The actual component-compactness premise is confined to this implication. -/
theorem small_diagram_presentable (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable M κLP] (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hS : HasCardinalLT (Arrow S) χ)
    (hF : ∀ s : S, IsCardinalPresentable (F.obj s) χ) :
    IsCardinalPresentable F χ := by
  let (s : S) : IsCardinalPresentable (F.obj s) χ := hF s
  let hCoy (s : S) : (uliftCoyoneda.{w}.obj (op (F.obj s))).IsCardinalAccessible χ :=
    (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{w} (F.obj s) χ).1 (hF s)
  let hEval (s : S) : ((evaluation S M).obj s).IsCardinalAccessible χ :=
    { preservesColimitOfShape J _ _ := by
        let : HasColimitsOfShape J M := inferInstance
        infer_instance }
  have hLeft (s : S) : ((equationIndex M F).left s).IsCardinalAccessible χ := by
    let : ((evaluation S M).obj s).IsCardinalAccessible χ := hEval s
    let : (uliftCoyoneda.{w}.obj (op (F.obj s))).IsCardinalAccessible χ := hCoy s
    exact inferInstanceAs
      (((evaluation S M).obj s ⋙ uliftCoyoneda.{w}.obj (op (F.obj s))).IsCardinalAccessible χ)
  have hRight (f : Arrow S) : ((equationIndex M F).right f).IsCardinalAccessible χ := by
    let : ((evaluation S M).obj f.right).IsCardinalAccessible χ := hEval f.right
    let : (uliftCoyoneda.{w}.obj (op (F.obj f.left))).IsCardinalAccessible χ := hCoy f.left
    exact inferInstanceAs (((evaluation S M).obj f.right ⋙
      uliftCoyoneda.{w}.obj (op (F.obj f.left))).IsCardinalAccessible χ)
  let (k : WalkingMulticospan (multicospanShapeEnd S)) :
      ((equationIndex M F).multicospan.obj k).IsCardinalAccessible χ := by
    cases k with
    | left s => exact hLeft s
    | right f => exact hRight f
  have h := Functor.isCardinalAccessible_of_isLimit (componentCone M F)
    (componentConeIsLimit M F) χ (endShapeArrow_bound χ hS)
  exact h

end SmallDiagrams


section OriginalComponents

variable (M : Type uM) [Category.{vM} M] (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable M κLP]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

include s in
/-- Every ORIGINAL component of a compact original diagram is compact at the bounded rank.
The SAME evaluation/cofree adjunction and actual Hom bound supply its preservation proof. -/
theorem component_presentable (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hLP : κLP ≤ χ) (hD : HasCardinalLT (Arrow S) χ)
    (F : D ⥤ M) [IsCardinalPresentable F χ] (d : D) :
    IsCardinalPresentable (F.obj d) χ := by
  let : (Completeness.cofree M κLP s d).IsCardinalAccessible χ :=
    HomPowerAccessibility.cofree_isCardinalAccessible_of_hom_bounds M κLP s d χ hLP
      (fun e ↦ HomPowerAccessibility.hom_bound_of_representative_arrows s χ hD d e)
  exact Adjunction.isCardinalPresentable_leftAdjoint_obj
    (Completeness.evaluationCofreeAdjunction M κLP s d) χ F


include κLP s in
/-- Suppose `M` is κLP-locally presentable at regular κLP, `s : D ≌ S`
identifies the index with a small category, and χ is regular. If |Arrow S| < χ
and every original component `F.obj d` is χ-presentable, then the whole
original diagram `F : D ⥤ M` is χ-presentable. This direction does not require
κLP ≤ χ. -/
theorem diagram_presentable (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M)
    (hF : ∀ d : D, IsCardinalPresentable (F.obj d) χ) :
    IsCardinalPresentable F χ := by
  let E := s.congrLeft (E := M)
  let : IsCardinalPresentable (E.functor.obj F) χ :=
    small_diagram_presentable M (E.functor.obj F) κLP χ hD
      (fun t ↦ hF (s.inverse.obj t))
  exact (isCardinalPresentable_iff_of_isEquivalence F χ E.functor).1 inferInstance

include s in
/-- For κLP-locally presentable `M` at regular κLP, a small-category
equivalence `s : D ≌ S`, and regular χ with κLP ≤ χ and |Arrow S| < χ,
`F : D ⥤ M` is χ-presentable if and only if every original component
`F.obj d` is χ-presentable. The rank inequality is required for the
diagram-to-components direction; the reverse direction needs no such
inequality. -/
theorem presentable_iff_components (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hLP : κLP ≤ χ) (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M) :
    IsCardinalPresentable F χ ↔ ∀ d : D, IsCardinalPresentable (F.obj d) χ := by
  constructor
  · intro h
    let : IsCardinalPresentable F χ := h
    exact fun d ↦ component_presentable M κLP s χ hLP hD F d
  · exact diagram_presentable M κLP s χ hD F


end OriginalComponents

end CategoryTheory.Presentable.FunctorPresentability
