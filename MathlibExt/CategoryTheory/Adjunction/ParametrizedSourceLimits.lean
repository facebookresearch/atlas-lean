/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Source mapping limits from the actual tensor adjunctions

A parametrized adjunction supplies the entire source Hom correspondence.
The original tensor functors preserve colimits because their actual right
adjunctions are given. Mathlib's transposed-cocone construction then proves
source limit preservation at every size, with all categorical data fixed.

For a caller's particular pushout, we also retain the actual tensor-image
pushout desc, its two legs, the complete compatible-pair Hom equivalence,
both round trips, and coefficient and target naturality. The construction
uses no separately supplied mapping pullback or source-limit packet.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃ w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ParametrizedAdjunction

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  (adj : F ⊣₂ G) (R : C₂ → C₃ ⥤ C₁)
  (tensorAdj : ∀ T, F.flip.obj T ⊣ R T)

include adj tensorAdj in
/-- Actual tensor adjunctions and the full parametrized Hom naturality
prove preservation of every source limit, with independent shape sizes. -/
theorem source_preservesLimitsOfSize (E : C₃) :
    PreservesLimitsOfSize.{w, w'} (G.flip.obj E) where
  preservesLimitsOfShape {J} _ := by
    let (T : C₂) : PreservesColimitsOfShape Jᵒᵖ (F.flip.obj T) :=
      (tensorAdj T).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact adj.preservesLimitsOfShape_flip_obj J E

section ChosenPushout

variable {A B Z C : C₁} (i : A ⟶ B) (z : A ⟶ Z)
  (kB : B ⟶ C) (kZ : Z ⟶ C) (sq : IsPushout i z kB kZ)

include tensorAdj sq in
/-- The actual tensor image of the caller's same pushout is a pushout. -/
theorem sourceTensorPushout (T : C₂) :
    IsPushout ((F.map i).app T) ((F.map z).app T)
      ((F.map kB).app T) ((F.map kZ).app T) := by
  let _ : PreservesColimitsOfSize.{0, 0} (F.flip.obj T) :=
    (tensorAdj T).leftAdjoint_preservesColimits
  exact sq.map (F.flip.obj T)

include adj tensorAdj sq in
/-- The full source mapping square is a pullback of the caller's
original maps; all four legs come from that same original pushout. -/
theorem sourcePushout_pullback (E : C₃) :
    IsPullback ((G.map kB.op).app E) ((G.map kZ.op).app E)
      ((G.map i.op).app E) ((G.map z.op).app E) := by
  let _ : PreservesLimitsOfSize.{0, 0} (G.flip.obj E) :=
    source_preservesLimitsOfSize adj R tensorAdj E
  exact (sq.op.map (G.flip.obj E)).flip

variable (E : C₃) (T : C₂)

/-- Compatible maps keep both full original source functions. -/
def sourceCompatibleMaps :=
  { ab : (T ⟶ (G.obj (op B)).obj E) × (T ⟶ (G.obj (op Z)).obj E) //
      ab.1 ≫ (G.map i.op).app E = ab.2 ≫ (G.map z.op).app E }

/-- Compatibility of the actual full inverse transposes follows from
the original source naturality of the parametrized adjunction. -/
theorem sourceTranspose_compatible
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    (F.map i).app T ≫ adj.homEquiv.symm a =
      (F.map z).app T ≫ adj.homEquiv.symm b := by
  rw [← adj.homEquiv_symm_naturality_one,
    ← adj.homEquiv_symm_naturality_one, h]

/-- Transpose both inputs and descend through the actual tensor
image of the caller's pushout, retaining its two original quotient legs. -/
def sourceTensorDesc
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    (F.obj C).obj T ⟶ E :=
  (sourceTensorPushout R tensorAdj i z kB kZ sq T).desc
    (adj.homEquiv.symm a) (adj.homEquiv.symm b)
    (sourceTranspose_compatible adj i z E T a b h)

/-- The first entire tensor-desc leg is the original inverse Hom function. -/
theorem sourceTensorDesc_first
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    (F.map kB).app T ≫ sourceTensorDesc adj R tensorAdj i z kB kZ sq E T a b h =
      adj.homEquiv.symm a :=
  (sourceTensorPushout R tensorAdj i z kB kZ sq T).inl_desc _ _ _

/-- The second entire tensor-desc leg is the original inverse Hom function. -/
theorem sourceTensorDesc_second
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    (F.map kZ).app T ≫ sourceTensorDesc adj R tensorAdj i z kB kZ sq E T a b h =
      adj.homEquiv.symm b :=
  (sourceTensorPushout R tensorAdj i z kB kZ sq T).inr_desc _ _ _

/-- The inverse compatible-pair function is the full original Hom
transpose of the actual tensor-image pushout desc. -/
def sourceLift
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    T ⟶ (G.obj (op C)).obj E :=
  adj.homEquiv (sourceTensorDesc adj R tensorAdj i z kB kZ sq E T a b h)

/-- The first entire source lift projection is the caller's first map. -/
theorem sourceLift_first
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    sourceLift adj R tensorAdj i z kB kZ sq E T a b h ≫ (G.map kB.op).app E = a := by
  rw [sourceLift, ← adj.homEquiv_naturality_one,
    sourceTensorDesc_first, Equiv.apply_symm_apply]

/-- The second entire source lift projection is the caller's second map. -/
theorem sourceLift_second
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    sourceLift adj R tensorAdj i z kB kZ sq E T a b h ≫ (G.map kZ.op).app E = b := by
  rw [sourceLift, ← adj.homEquiv_naturality_one,
    sourceTensorDesc_second, Equiv.apply_symm_apply]

/-- The explicit tensor-desc construction equals the lift of the
same preserved source pullback, by both actual original projections. -/
theorem sourceLift_eq_pullbackLift
    (a : T ⟶ (G.obj (op B)).obj E) (b : T ⟶ (G.obj (op Z)).obj E)
    (h : a ≫ (G.map i.op).app E = b ≫ (G.map z.op).app E) :
    sourceLift adj R tensorAdj i z kB kZ sq E T a b h =
      (sourcePushout_pullback adj R tensorAdj i z kB kZ sq E).lift a b h := by
  apply (sourcePushout_pullback adj R tensorAdj i z kB kZ sq E).hom_ext
  · rw [sourceLift_first, IsPullback.lift_fst]
  · rw [sourceLift_second, IsPullback.lift_snd]

/-- The complete source Hom equivalence keeps both original legs
and the actual tensor-desc inverse, with both full round trips. -/
def sourcePushoutHomEquiv :
    (T ⟶ (G.obj (op C)).obj E) ≃ sourceCompatibleMaps (G := G) i z E T where
  toFun h := ⟨(h ≫ (G.map kB.op).app E, h ≫ (G.map kZ.op).app E), by
    rw [Category.assoc, Category.assoc,
      (sourcePushout_pullback adj R tensorAdj i z kB kZ sq E).w]⟩
  invFun ab := sourceLift adj R tensorAdj i z kB kZ sq E T ab.1.1 ab.1.2 ab.2
  left_inv h := by
    apply (sourcePushout_pullback adj R tensorAdj i z kB kZ sq E).hom_ext
    · exact sourceLift_first adj R tensorAdj i z kB kZ sq E T _ _ _
    · exact sourceLift_second adj R tensorAdj i z kB kZ sq E T _ _ _
  right_inv ab := by
    apply Subtype.ext
    exact Prod.ext
      (sourceLift_first adj R tensorAdj i z kB kZ sq E T _ _ _)
      (sourceLift_second adj R tensorAdj i z kB kZ sq E T _ _ _)

/-- The entire forward Hom function is the pair of the actual original projections. -/
theorem sourcePushoutHomEquiv_forward_function :
    (fun h => (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T h).1) =
      fun h => (h ≫ (G.map kB.op).app E, h ≫ (G.map kZ.op).app E) := rfl

/-- The entire inverse Hom function is the original tensor/end
transpose of the actual two-legged pushout desc. -/
theorem sourcePushoutHomEquiv_inverse_function :
    ((sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T).symm : _ → _) =
      fun ab => adj.homEquiv
        (sourceTensorDesc adj R tensorAdj i z kB kZ sq E T ab.1.1 ab.1.2 ab.2) := rfl

variable {E T}

/-- Coefficient precomposition preserves the full compatible pair. -/
def sourceCompatiblePrecompose {T' : C₂} (r : T' ⟶ T)
    (ab : sourceCompatibleMaps (G := G) i z E T) :
    sourceCompatibleMaps (G := G) i z E T' :=
  ⟨(r ≫ ab.1.1, r ≫ ab.1.2), by
    simp only [Category.assoc]
    exact congrArg (fun f => r ≫ f) ab.2⟩

/-- Every coefficient map preserves the entire forward Hom function. -/
theorem sourcePushoutHomEquiv_coefficient
    {T' : C₂} (r : T' ⟶ T) (h : T ⟶ (G.obj (op C)).obj E) :
    sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T' (r ≫ h) =
      sourceCompatiblePrecompose i z r
        (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T h) := by
  apply Subtype.ext
  exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Every coefficient map also preserves the complete tensor-desc inverse function. -/
theorem sourcePushoutHomEquiv_inverse_coefficient
    {T' : C₂} (r : T' ⟶ T) (ab : sourceCompatibleMaps (G := G) i z E T) :
    (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T').symm
        (sourceCompatiblePrecompose i z r ab) =
      r ≫ (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T).symm ab := by
  apply (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T').injective
  rw [Equiv.apply_symm_apply, sourcePushoutHomEquiv_coefficient,
    Equiv.apply_symm_apply]

/-- Original target maps preserve both compatible source functions. -/
def sourceCompatiblePostcompose {E' : C₃} (g : E ⟶ E')
    (ab : sourceCompatibleMaps (G := G) i z E T) :
    sourceCompatibleMaps (G := G) i z E' T :=
  ⟨(ab.1.1 ≫ (G.obj (op B)).map g, ab.1.2 ≫ (G.obj (op Z)).map g), by
    rw [Category.assoc, (G.map i.op).naturality, ← Category.assoc, ab.2,
      Category.assoc, ← (G.map z.op).naturality, ← Category.assoc]⟩

/-- Every target map preserves the whole forward source Hom function. -/
theorem sourcePushoutHomEquiv_target
    {E' : C₃} (g : E ⟶ E') (h : T ⟶ (G.obj (op C)).obj E) :
    sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E' T
        (h ≫ (G.obj (op C)).map g) =
      sourceCompatiblePostcompose i z g
        (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T h) := by
  apply Subtype.ext
  apply Prod.ext
  · exact Category.assoc _ _ _ |>.trans
      (congrArg (fun f => h ≫ f) ((G.map kB.op).naturality g)) |>.trans
      (Category.assoc _ _ _).symm
  · exact Category.assoc _ _ _ |>.trans
      (congrArg (fun f => h ≫ f) ((G.map kZ.op).naturality g)) |>.trans
      (Category.assoc _ _ _).symm

/-- Every target map also preserves the entire tensor-desc inverse function. -/
theorem sourcePushoutHomEquiv_inverse_target
    {E' : C₃} (g : E ⟶ E') (ab : sourceCompatibleMaps (G := G) i z E T) :
    (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E' T).symm
        (sourceCompatiblePostcompose i z g ab) =
      (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E T).symm ab ≫
        (G.obj (op C)).map g := by
  apply (sourcePushoutHomEquiv adj R tensorAdj i z kB kZ sq E' T).injective
  rw [Equiv.apply_symm_apply, sourcePushoutHomEquiv_target, Equiv.apply_symm_apply]

end ChosenPushout

end CategoryTheory.ParametrizedAdjunction
