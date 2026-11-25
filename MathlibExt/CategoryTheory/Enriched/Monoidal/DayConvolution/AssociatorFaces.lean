/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped

/-!
# Original nested Day relation faces

The left and right nested presentations retain the complete index Hom objects,
their original object and relation families, and the actual inner projections.
The compatibility equations are derived from these maps and genuine colimit laws.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uA uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorFaces

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

omit [MonoidalClosed V] in
@[reassoc]
private theorem symmetricTensorInterchange (R S X Y : V) :
    (β_ (R ⊗ S) (X ⊗ Y)).hom ≫ tensorμ X Y R S =
      tensorμ R S X Y ≫ ((β_ R X).hom ⊗ₘ (β_ S Y).hom) := by
  simp only [tensorμ, BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, tensorHom_def, Category.assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding R Y]
  monoidal
  simp

omit [MonoidalClosed V] in
private theorem tensorActionWord {X X' Y Y' Z Z' : V} (R S : V)
    (g : X ⟶ X') (h : Y ⟶ Y') (a : X' ⊗ R ⟶ Z) (b : Y' ⊗ S ⟶ Z') :
    (R ⊗ S) ◁ (g ⊗ₘ h) ≫ (β_ (R ⊗ S) (X' ⊗ Y')).hom ≫
        tensorμ X' Y' R S ≫ (a ⊗ₘ b) =
      tensorμ R S X Y ≫
        (((β_ R X).hom ≫ g ▷ R ≫ a) ⊗ₘ ((β_ S Y).hom ≫ h ▷ S ≫ b)) := by
  rw [BraidedCategory.braiding_naturality_right_assoc, tensorμ_natural_left_assoc,
    symmetricTensorInterchange_assoc]
  simp only [tensorHom_comp_tensorHom]

section LeftNested

universe uC1 uC2 uK uE uM
variable {C1 : Type uC1} [EnrichedCategory V C1]
  {C2 : Type uC2} [EnrichedCategory V C2]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
  {M : Type uM} [EnrichedCategory V M]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (K × E) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

namespace Left

/-- Literal outer object word, with the inner coend slot retained. -/
abbrev objectFunctor (p : K × E) : V ⥤ V :=
  tensorRight (H.obj p.2) ⋙ tensorLeft ((EnrichedDayKernel.weight U m).obj (op p))

/-- Literal outer relation word, with its full original product Hom. -/
abbrev relationFunctor (p q : K × E) : V ⥤ V :=
  tensorRight (H.obj p.2) ⋙ tensorLeft (p ⟶[V] q) ⋙
    tensorLeft ((EnrichedDayKernel.weight U m).obj (op q))

/-- The original left-nested object family before its inner coend projection. -/
abbrev objects (p : K × E) (i : C1 × C2) : V :=
  (objectFunctor U H m p).obj (EnrichedDayKernel.objects T F1 F2 p.1 i)

/-- The original left-nested inner relation family, retaining its complete inner Hom object. -/
abbrev innerRelations (p : K × E) (ij : (C1 × C2) × (C1 × C2)) : V :=
  (objectFunctor U H m p).obj (EnrichedDayKernel.relations T F1 F2 p.1 ij)

/-- The original left outer relation family, retaining the complete outer product Hom. -/
abbrev outerRelations (p q : K × E) (i : C1 × C2) : V :=
  (relationFunctor U H m p q).obj (EnrichedDayKernel.objects T F1 F2 p.1 i)

/-- The left mixed relation family, retaining both original inner and outer Hom objects. -/
abbrev mixedRelations (p q : K × E) (ij : (C1 × C2) × (C1 × C2)) : V :=
  (relationFunctor U H m p q).obj (EnrichedDayKernel.relations T F1 F2 p.1 ij)

/-- Map the original inner weight face through the actual left outer coefficient tensor. -/
abbrev b0 (p : K × E) (i j : C1 × C2) :
    innerRelations T U F1 F2 H m p (i, j) ⟶ objects T U F1 F2 H m p i :=
  (objectFunctor U H m p).map
    (Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j)

/-- Map the original inner diagram-action face through the actual left outer coefficient tensor. -/
abbrev b1 (p : K × E) (i j : C1 × C2) :
    innerRelations T U F1 F2 H m p (i, j) ⟶ objects T U F1 F2 H m p j :=
  (objectFunctor U H m p).map
    (Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j)

/-- Map the original inner weight face through the full left outer relation word. -/
abbrev r0 (p q : K × E) (i j : C1 × C2) :
    mixedRelations T U F1 F2 H m p q (i, j) ⟶ outerRelations T U F1 F2 H m p q i :=
  (relationFunctor U H m p q).map
    (Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j)

/-- Map the original inner diagram-action face through the full left outer relation word. -/
abbrev r1 (p q : K × E) (i j : C1 × C2) :
    mixedRelations T U F1 F2 H m p q (i, j) ⟶ outerRelations T U F1 F2 H m p q j :=
  (relationFunctor U H m p q).map
    (Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j)

/-- The original left outer weight face on each unprojected inner generator. -/
abbrev a0 (p q : K × E) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶ objects T U F1 F2 H m p i :=
  (α_ ((EnrichedDayKernel.weight U m).obj (op q)) (p ⟶[V] q)
    (EnrichedDayKernel.objects T F1 F2 p.1 i ⊗ H.obj p.2)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (EnrichedDayKernel.objects T F1 F2 p.1 i ⊗ H.obj p.2))

/-- The inner action retains the original entire output Hom and coefficient word. -/
abbrev a1 (p q : K × E) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶ objects T U F1 F2 H m q i :=
  ((EnrichedDayKernel.weight U m).obj (op q)) ◁
    (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2)
        (EnrichedDayKernel.objects T F1 F2 p.1 i) (H.obj p.2) ≫
      (EnrichedDayKernel.Output.outputAction (T.obj i) p.1 q.1
          (F1.obj i.1 ⊗ F2.obj i.2) ⊗ₘ
        ((β_ (p.2 ⟶[V] q.2) (H.obj p.2)).hom ≫ MonoidalClosed.uncurry (H.map p.2 q.2))))

/-- The original outer weight face is natural in its actual inner coefficient slot. -/
private def face0Transformation (p q : K × E) :
    relationFunctor U H m p q ⟶ objectFunctor U H m p where
  app A :=
    (α_ ((EnrichedDayKernel.weight U m).obj (op q)) (p ⟶[V] q) (A ⊗ H.obj p.2)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (A ⊗ H.obj p.2))
  naturality A B f := by
    rw [Category.assoc]
    let Wq := (EnrichedDayKernel.weight U m).obj (op q)
    let Wp := (EnrichedDayKernel.weight U m).obj (op p)
    let R := p ⟶[V] q
    let h := H.obj p.2
    let t : Wq ⊗ R ⟶ Wp :=
      MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p))
    change Wq ◁ (R ◁ (f ▷ h)) ≫ (α_ Wq R (B ⊗ h)).inv ≫
      (t ⊗ₘ 𝟙 (B ⊗ h)) =
        (α_ Wq R (A ⊗ h)).inv ≫ (t ⊗ₘ 𝟙 (A ⊗ h)) ≫ Wp ◁ (f ▷ h)
    rw [associator_inv_naturality_right_assoc]
    simpa only [tensorHom_id, Category.assoc] using
      congrArg (fun s => (α_ Wq R (A ⊗ h)).inv ≫ s) (whisker_exchange t (f ▷ h))

private theorem face0Transformation_app (p q : K × E) (i : C1 × C2) :
    (face0Transformation U H m p q).app (EnrichedDayKernel.objects T F1 F2 p.1 i) =
      a0 T U F1 F2 H m p q i := rfl

/-- The original inner projection, transported by the actual outer coefficient tensor. -/
abbrev innerGenerator (p : K × E)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.1)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.1)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.1)
      (EnrichedDayKernel.rightMap T F1 F2 p.1)] (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶
      (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.1) :=
  (objectFunctor U H m p).map (EnrichedDayKernel.gen T F1 F2 p.1 i)

/-- The entire first outer face respects the original inner relation. -/
theorem outerFace0_innerGenerator (p q : K × E)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.1)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.1)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.1)
      (EnrichedDayKernel.rightMap T F1 F2 p.1)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m p i =
      r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m p j :=
  Enriched.weightedCoend.Mapped.projectedFacesNaturality
    (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2)
    (relationFunctor U H m p q) (objectFunctor U H m p)
    (face0Transformation U H m p q) i j

/-- The uncurried H-action with its complete outer coefficient Hom object placed first. -/
abbrev coefficientAction (p q : K × E) : (p.2 ⟶[V] q.2) ⊗ H.obj p.2 ⟶ H.obj q.2 :=
  (β_ (p.2 ⟶[V] q.2) (H.obj p.2)).hom ≫ MonoidalClosed.uncurry (H.map p.2 q.2)

theorem a1_innerGenerator (p q : K × E)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.1)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.1)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.1)
      (EnrichedDayKernel.rightMap T F1 F2 q.1)] (i : C1 × C2) :
    a1 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m q i =
      ((EnrichedDayKernel.weight U m).obj (op q)) ◁
        (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2)
            (EnrichedDayKernel.objects T F1 F2 p.1 i) (H.obj p.2) ≫
          (EnrichedDayKernel.Output.actionGenerator T F1 F2 p.1 q.1 i ⊗ₘ
            coefficientAction H p q)) := by
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  let A := EnrichedDayKernel.objects T F1 F2 p.1 i
  let B := EnrichedDayKernel.objects T F1 F2 q.1 i
  let a : (p.1 ⟶[V] q.1) ⊗ A ⟶ B :=
    EnrichedDayKernel.Output.outputAction (T.obj i) p.1 q.1 (F1.obj i.1 ⊗ F2.obj i.2)
  let g : B ⟶ EnrichedDayKernel.obj T F1 F2 q.1 := EnrichedDayKernel.gen T F1 F2 q.1 i
  let b := coefficientAction H p q
  change Wq ◁ (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) A (H.obj p.2) ≫ (a ⊗ₘ b)) ≫
    Wq ◁ (g ▷ H.obj q.2) =
      Wq ◁ (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) A (H.obj p.2) ≫ ((a ≫ g) ⊗ₘ b))
  rw [← tensorHom_id, ← MonoidalCategory.whiskerLeft_comp, Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id]

private theorem innerAction_balanced (s s' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 s')]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 s')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 s')
      (EnrichedDayKernel.rightMap T F1 F2 s')] (i j : C1 × C2) :
    (s ⟶[V] s') ◁ Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T s)
        (F1.externalTensor F2) i j ≫
        EnrichedDayKernel.Output.actionGenerator T F1 F2 s s' i =
      (s ⟶[V] s') ◁ Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T s)
        (F1.externalTensor F2) i j ≫
        EnrichedDayKernel.Output.actionGenerator T F1 F2 s s' j := by
  have h := EnrichedDayKernel.Output.actionGenerator_balanced T F1 F2 s s' i j
  have h' := congrArg MonoidalClosed.uncurry h
  simpa only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    Enriched.weightedCoend.face0, Enriched.weightedCoend.face1] using h'

theorem outerFace1_innerGenerator (p q : K × E)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.1)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.1)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.1)
      (EnrichedDayKernel.rightMap T F1 F2 q.1)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m q i =
      r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m q j := by
  let R := p.1 ⟶[V] q.1
  let S := p.2 ⟶[V] q.2
  let B := H.obj p.2
  let Z := EnrichedDayKernel.relations T F1 F2 p.1 (i, j)
  let l := Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j
  let r := Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.1) (F1.externalTensor F2) i j
  let gi := EnrichedDayKernel.Output.actionGenerator T F1 F2 p.1 q.1 i
  let gj := EnrichedDayKernel.Output.actionGenerator T F1 F2 p.1 q.1 j
  let b := coefficientAction H p q
  have hi :
      (R ⊗ S) ◁ (l ⊗ₘ 𝟙 B) ≫
          tensorμ R S (EnrichedDayKernel.objects T F1 F2 p.1 i) B ≫ (gi ⊗ₘ b) =
        tensorμ R S Z B ≫ ((R ◁ l ≫ gi) ⊗ₘ b) := by
    simpa only [id_tensorHom_id, id_tensorHom, tensorHom_comp_tensorHom,
      MonoidalCategory.whiskerLeft_id, Category.id_comp] using
      tensorμ_natural_right_assoc R S l (𝟙 B) (gi ⊗ₘ b)
  have hj :
      (R ⊗ S) ◁ (r ⊗ₘ 𝟙 B) ≫
          tensorμ R S (EnrichedDayKernel.objects T F1 F2 p.1 j) B ≫ (gj ⊗ₘ b) =
        tensorμ R S Z B ≫ ((R ◁ r ≫ gj) ⊗ₘ b) := by
    simpa only [id_tensorHom_id, id_tensorHom, tensorHom_comp_tensorHom,
      MonoidalCategory.whiskerLeft_id, Category.id_comp] using
      tensorμ_natural_right_assoc R S r (𝟙 B) (gj ⊗ₘ b)
  have hb : R ◁ l ≫ gi = R ◁ r ≫ gj := innerAction_balanced T F1 F2 p.1 q.1 i j
  rw [a1_innerGenerator, a1_innerGenerator]
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  change Wq ◁ ((R ⊗ S) ◁ (l ▷ B)) ≫
      Wq ◁ (tensorμ R S (EnrichedDayKernel.objects T F1 F2 p.1 i) B ≫ (gi ⊗ₘ b)) =
    Wq ◁ ((R ⊗ S) ◁ (r ▷ B)) ≫
      Wq ◁ (tensorμ R S (EnrichedDayKernel.objects T F1 F2 p.1 j) B ≫ (gj ⊗ₘ b))
  rw [← tensorHom_id, ← tensorHom_id]
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
    hi, hj, hb]

section InnerQuotient

variable (p : K × E)
  [HasCoproduct (objects T U F1 F2 H m p)]
  [HasCoproduct (innerRelations T U F1 F2 H m p)]

/-- The coproduct map of the original inner weight faces in the left object family. -/
abbrev innerLeftMap := Enriched.weightedCoend.Mapped.mappedLeftMap (EnrichedDayKernel.weight T p.1)
  (F1.externalTensor F2) (objectFunctor U H m p)

/-- The coproduct map of the original inner diagram-action faces in the left object family. -/
abbrev innerRightMap :=
  Enriched.weightedCoend.Mapped.mappedRightMap (EnrichedDayKernel.weight T p.1)
  (F1.externalTensor F2) (objectFunctor U H m p)

variable [HasCoequalizer (innerLeftMap T U F1 F2 H m p)
  (innerRightMap T U F1 F2 H m p)]

/-- The original quotient of the actual inner relation family. -/
abbrev innerPoint := coequalizer (innerLeftMap T U F1 F2 H m p)
  (innerRightMap T U F1 F2 H m p)

/-- The actual chosen inner coequalizer projection on its original generator. -/
abbrev innerProjection (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶ innerPoint T U F1 F2 H m p :=
  Sigma.ι (objects T U F1 F2 H m p) i ≫
    coequalizer.π (innerLeftMap T U F1 F2 H m p) (innerRightMap T U F1 F2 H m p)

variable [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.1)]
  [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.1)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.1)
    (EnrichedDayKernel.rightMap T F1 F2 p.1)]

/-- Closedness and the actual braid preserve precisely the original inner colimits. -/
@[no_expose]
def innerIso : innerPoint T U F1 F2 H m p ≅
    (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.1) := by
  let W := EnrichedDayKernel.weight T p.1
  let Q := F1.externalTensor F2
  let B := H.obj p.2
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.objects W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.relations W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit
      (parallelPair (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso W Q (objectFunctor U H m p)

@[reassoc]
theorem innerProjection_iso (i : C1 × C2) :
    innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom =
      innerGenerator T U F1 F2 H m p i := by
  let W := EnrichedDayKernel.weight T p.1
  let Q := F1.externalTensor F2
  let B := H.obj p.2
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.objects W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.relations W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit
      (parallelPair (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso_generator W Q (objectFunctor U H m p) i

theorem outerFace0_innerProjection (q : K × E) (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerProjection T U F1 F2 H m p i =
      r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerProjection T U F1 F2 H m p j := by
  apply (cancel_mono (innerIso T U F1 F2 H m p).hom).1
  calc
    _ = r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m p i := by
      rw [Category.assoc, Category.assoc, innerProjection_iso]
    _ = r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m p j := outerFace0_innerGenerator T U F1 F2 H m p q i j
    _ = _ := by
      symm
      rw [Category.assoc, Category.assoc, innerProjection_iso]

end InnerQuotient

theorem outerFace1_innerProjection (p q : K × E)
    [HasCoproduct (objects T U F1 F2 H m q)]
    [HasCoproduct (innerRelations T U F1 F2 H m q)]
    [HasCoequalizer (innerLeftMap T U F1 F2 H m q) (innerRightMap T U F1 F2 H m q)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.1)]
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.1)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.1)
      (EnrichedDayKernel.rightMap T F1 F2 q.1)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerProjection T U F1 F2 H m q i =
      r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerProjection T U F1 F2 H m q j := by
  apply (cancel_mono (innerIso T U F1 F2 H m q).hom).1
  calc
    _ = r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m q i := by
      rw [Category.assoc, Category.assoc, innerProjection_iso]
    _ = r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m q j := outerFace1_innerGenerator T U F1 F2 H m p q i j
    _ = _ := by
      symm
      rw [Category.assoc, Category.assoc, innerProjection_iso]

section OriginalOuterFaces

variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]

/-- The actual left parent diagram: the original inner kernel output functor tensored with H. -/
abbrev originalOuterDiagram := (EnrichedDayKernel.Output.functor T F1 F2).externalTensor H

/-- The relation generator maps into the actual parent Day relation word. -/
abbrev relationGenerator (p q : K × E) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶
      Enriched.weightedCoend.relations (EnrichedDayKernel.weight U m)
        (originalOuterDiagram T F1 F2 H) (p, q) :=
  (relationFunctor U H m p q).map (EnrichedDayKernel.gen T F1 F2 p.1 i)

/-- The raw weight face is the original outer Day weight face on every generator. -/
theorem originalOuterFace0 (p q : K × E) (i : C1 × C2) :
    relationGenerator T U F1 F2 H m p q i ≫
        Enriched.weightedCoend.face0 (EnrichedDayKernel.weight U m)
          (originalOuterDiagram T F1 F2 H) p q =
      a0 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m p i :=
  (face0Transformation U H m p q).naturality (EnrichedDayKernel.gen T F1 F2 p.1 i)

/-- The hom-first word agrees with the full original external-tensor Day action. -/
theorem originalOuterFace1 (p q : K × E) (i : C1 × C2) :
    relationGenerator T U F1 F2 H m p q i ≫
        Enriched.weightedCoend.face1 (EnrichedDayKernel.weight U m)
          (originalOuterDiagram T F1 F2 H) p q =
      a1 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m q i := by
  rw [a1_innerGenerator]
  simp only [Enriched.weightedCoend.face1, EnrichedFunctor.externalTensor_uncurry]
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  let R := p.1 ⟶[V] q.1
  let S := p.2 ⟶[V] q.2
  let X := EnrichedDayKernel.objects T F1 F2 p.1 i
  let Q := EnrichedDayKernel.obj T F1 F2 p.1
  let B := H.obj p.2
  let g : X ⟶ Q := EnrichedDayKernel.gen T F1 F2 p.1 i
  let a := MonoidalClosed.uncurry (EnrichedDayKernel.Output.map T F1 F2 p.1 q.1)
  let b := MonoidalClosed.uncurry (H.map p.2 q.2)
  change Wq ◁ ((R ⊗ S) ◁ (g ▷ B)) ≫
      Wq ◁ ((β_ (R ⊗ S) (Q ⊗ B)).hom ≫ tensorμ Q B R S ≫ (a ⊗ₘ b)) =
    Wq ◁ (tensorμ R S X B ≫
      (EnrichedDayKernel.Output.actionGenerator T F1 F2 p.1 q.1 i ⊗ₘ
        ((β_ S B).hom ≫ b)))
  rw [← MonoidalCategory.whiskerLeft_comp]
  have h := tensorActionWord R S g (𝟙 B) a b
  simp only [tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp] at h
  have hn := EnrichedDayKernel.Output.gen_naturality T F1 F2 p.1 q.1 i
  simp only [tensorHom_id] at hn
  rw [hn] at h
  exact congrArg (fun f => Wq ◁ f) h

section NestedGenerator

variable [HasCoproduct (EnrichedDayKernel.objects U
    (EnrichedDayKernel.Output.functor T F1 F2) H m)]
  [HasCoproduct (EnrichedDayKernel.relations U
    (EnrichedDayKernel.Output.functor T F1 F2) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U
    (EnrichedDayKernel.Output.functor T F1 F2) H m)
    (EnrichedDayKernel.rightMap U (EnrichedDayKernel.Output.functor T F1 F2) H m)]

/-- The full original left-nested Day generator, including both original coend legs. -/
abbrev nestedGenerator (p : K × E) (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶
      EnrichedDayKernel.obj U (EnrichedDayKernel.Output.functor T F1 F2) H m :=
  innerGenerator T U F1 F2 H m p i ≫
    EnrichedDayKernel.gen U (EnrichedDayKernel.Output.functor T F1 F2) H m p

theorem nestedGenerator_innerProjection (p : K × E)
    [HasCoproduct (objects T U F1 F2 H m p)]
    [HasCoproduct (innerRelations T U F1 F2 H m p)]
    [HasCoequalizer (innerLeftMap T U F1 F2 H m p) (innerRightMap T U F1 F2 H m p)]
    (i : C1 × C2) :
    innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom ≫
        EnrichedDayKernel.gen U (EnrichedDayKernel.Output.functor T F1 F2) H m p =
      nestedGenerator T U F1 F2 H m p i := by
  let g : (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.1) ⟶
      EnrichedDayKernel.obj U (EnrichedDayKernel.Output.functor T F1 F2) H m :=
    EnrichedDayKernel.gen U (EnrichedDayKernel.Output.functor T F1 F2) H m p
  change innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom ≫ g =
    innerGenerator T U F1 F2 H m p i ≫ g
  rw [← Category.assoc, innerProjection_iso]

end NestedGenerator

end OriginalOuterFaces

end Left
end LeftNested

section RightNested

universe uC1' uC2' uK' uE' uM'
variable {C1 : Type uC1'} [EnrichedCategory V C1]
  {C2 : Type uC2'} [EnrichedCategory V C2]
  {K : Type uK'} [EnrichedCategory V K]
  {E : Type uE'} [EnrichedCategory V E]
  {M : Type uM'} [EnrichedCategory V M]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (E × K) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

namespace Right

/-- Tensor the actual inner object first by H and then by its original right outer weight. -/
abbrev objectFunctor (p : E × K) : V ⥤ V :=
  tensorLeft (H.obj p.1) ⋙ tensorLeft ((EnrichedDayKernel.weight U m).obj (op p))

/-- The actual right outer relation functor, retaining its complete original product Hom. -/
abbrev relationFunctor (p q : E × K) : V ⥤ V :=
  tensorLeft (H.obj p.1) ⋙ tensorLeft (p ⟶[V] q) ⋙
    tensorLeft ((EnrichedDayKernel.weight U m).obj (op q))

/-- The original right-nested object family before its inner coend projection. -/
abbrev objects (p : E × K) (i : C1 × C2) : V :=
  (objectFunctor U H m p).obj (EnrichedDayKernel.objects T F1 F2 p.2 i)

/-- The original right-nested inner relation family, retaining its complete inner Hom object. -/
abbrev innerRelations (p : E × K) (ij : (C1 × C2) × (C1 × C2)) : V :=
  (objectFunctor U H m p).obj (EnrichedDayKernel.relations T F1 F2 p.2 ij)

/-- The original right outer relation family, retaining the complete outer product Hom. -/
abbrev outerRelations (p q : E × K) (i : C1 × C2) : V :=
  (relationFunctor U H m p q).obj (EnrichedDayKernel.objects T F1 F2 p.2 i)

/-- The right mixed relation family, retaining both original inner and outer Hom objects. -/
abbrev mixedRelations (p q : E × K) (ij : (C1 × C2) × (C1 × C2)) : V :=
  (relationFunctor U H m p q).obj (EnrichedDayKernel.relations T F1 F2 p.2 ij)

/-- Map the original inner weight face through the actual right outer coefficient tensor. -/
abbrev b0 (p : E × K) (i j : C1 × C2) :
    innerRelations T U F1 F2 H m p (i, j) ⟶ objects T U F1 F2 H m p i :=
  (objectFunctor U H m p).map
    (Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j)

/-- Map the original inner diagram-action face through the actual right outer coefficient tensor. -/
abbrev b1 (p : E × K) (i j : C1 × C2) :
    innerRelations T U F1 F2 H m p (i, j) ⟶ objects T U F1 F2 H m p j :=
  (objectFunctor U H m p).map
    (Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j)

/-- Map the original inner weight face through the full right outer relation word. -/
abbrev r0 (p q : E × K) (i j : C1 × C2) :
    mixedRelations T U F1 F2 H m p q (i, j) ⟶ outerRelations T U F1 F2 H m p q i :=
  (relationFunctor U H m p q).map
    (Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j)

/-- Map the original inner diagram-action face through the full right outer relation word. -/
abbrev r1 (p q : E × K) (i j : C1 × C2) :
    mixedRelations T U F1 F2 H m p q (i, j) ⟶ outerRelations T U F1 F2 H m p q j :=
  (relationFunctor U H m p q).map
    (Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j)

/-- The original right outer weight face on each unprojected inner generator. -/
abbrev a0 (p q : E × K) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶ objects T U F1 F2 H m p i :=
  (α_ ((EnrichedDayKernel.weight U m).obj (op q)) (p ⟶[V] q)
    (H.obj p.1 ⊗ EnrichedDayKernel.objects T F1 F2 p.2 i)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (H.obj p.1 ⊗ EnrichedDayKernel.objects T F1 F2 p.2 i))

/-- The uncurried H-action with its complete outer coefficient Hom object placed first. -/
abbrev coefficientAction (p q : E × K) : (p.1 ⟶[V] q.1) ⊗ H.obj p.1 ⟶ H.obj q.1 :=
  (β_ (p.1 ⟶[V] q.1) (H.obj p.1)).hom ≫ MonoidalClosed.uncurry (H.map p.1 q.1)

/-- The right outer action word built from the full H-action and original inner output action. -/
abbrev a1 (p q : E × K) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶ objects T U F1 F2 H m q i :=
  ((EnrichedDayKernel.weight U m).obj (op q)) ◁
    (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2)
        (H.obj p.1) (EnrichedDayKernel.objects T F1 F2 p.2 i) ≫
      (coefficientAction H p q ⊗ₘ
        EnrichedDayKernel.Output.outputAction (T.obj i) p.2 q.2 (F1.obj i.1 ⊗ F2.obj i.2)))

private def face0Transformation (p q : E × K) :
    relationFunctor U H m p q ⟶ objectFunctor U H m p where
  app A :=
    (α_ ((EnrichedDayKernel.weight U m).obj (op q)) (p ⟶[V] q) (H.obj p.1 ⊗ A)).inv ≫
      (MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p)) ⊗ₘ
        𝟙 (H.obj p.1 ⊗ A))
  naturality A B f := by
    rw [Category.assoc]
    let Wq := (EnrichedDayKernel.weight U m).obj (op q)
    let Wp := (EnrichedDayKernel.weight U m).obj (op p)
    let R := p ⟶[V] q
    let h := H.obj p.1
    let t : Wq ⊗ R ⟶ Wp :=
      MonoidalClosed.uncurry ((EnrichedDayKernel.weight U m).map (op q) (op p))
    change Wq ◁ (R ◁ (h ◁ f)) ≫ (α_ Wq R (h ⊗ B)).inv ≫
      (t ⊗ₘ 𝟙 (h ⊗ B)) =
        (α_ Wq R (h ⊗ A)).inv ≫ (t ⊗ₘ 𝟙 (h ⊗ A)) ≫ Wp ◁ (h ◁ f)
    rw [associator_inv_naturality_right_assoc]
    simpa only [tensorHom_id, Category.assoc] using
      congrArg (fun s => (α_ Wq R (h ⊗ A)).inv ≫ s) (whisker_exchange t (h ◁ f))

/-- The original inner coend generator mapped by the actual right outer coefficient tensor. -/
abbrev innerGenerator (p : E × K)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.2)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.2)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.2)
      (EnrichedDayKernel.rightMap T F1 F2 p.2)] (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶
      (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.2) :=
  (objectFunctor U H m p).map (EnrichedDayKernel.gen T F1 F2 p.2 i)

theorem outerFace0_innerGenerator (p q : E × K)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.2)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.2)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.2)
      (EnrichedDayKernel.rightMap T F1 F2 p.2)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m p i =
      r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m p j :=
  Enriched.weightedCoend.Mapped.projectedFacesNaturality
    (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2)
    (relationFunctor U H m p q) (objectFunctor U H m p)
    (face0Transformation U H m p q) i j

theorem a1_innerGenerator (p q : E × K)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.2)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.2)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.2)
      (EnrichedDayKernel.rightMap T F1 F2 q.2)] (i : C1 × C2) :
    a1 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m q i =
      ((EnrichedDayKernel.weight U m).obj (op q)) ◁
        (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2)
            (H.obj p.1) (EnrichedDayKernel.objects T F1 F2 p.2 i) ≫
          (coefficientAction H p q ⊗ₘ
            EnrichedDayKernel.Output.actionGenerator T F1 F2 p.2 q.2 i)) := by
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  let A := EnrichedDayKernel.objects T F1 F2 p.2 i
  let B := EnrichedDayKernel.objects T F1 F2 q.2 i
  let a : (p.2 ⟶[V] q.2) ⊗ A ⟶ B :=
    EnrichedDayKernel.Output.outputAction (T.obj i) p.2 q.2 (F1.obj i.1 ⊗ F2.obj i.2)
  let g : B ⟶ EnrichedDayKernel.obj T F1 F2 q.2 := EnrichedDayKernel.gen T F1 F2 q.2 i
  let b := coefficientAction H p q
  change Wq ◁ (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) (H.obj p.1) A ≫ (b ⊗ₘ a)) ≫
    Wq ◁ (H.obj q.1 ◁ g) =
      Wq ◁ (tensorμ (p.1 ⟶[V] q.1) (p.2 ⟶[V] q.2) (H.obj p.1) A ≫ (b ⊗ₘ (a ≫ g)))
  have ht : (b ⊗ₘ a) ≫ H.obj q.1 ◁ g = b ⊗ₘ (a ≫ g) := by
    simpa only [id_tensorHom, Category.comp_id] using
      tensorHom_comp_tensorHom b a (𝟙 (H.obj q.1)) g
  rw [← MonoidalCategory.whiskerLeft_comp, Category.assoc, ht]

theorem outerFace1_innerGenerator (p q : E × K)
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.2)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.2)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.2)
      (EnrichedDayKernel.rightMap T F1 F2 q.2)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m q i =
      r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m q j := by
  let R := p.1 ⟶[V] q.1
  let S := p.2 ⟶[V] q.2
  let B := H.obj p.1
  let Z := EnrichedDayKernel.relations T F1 F2 p.2 (i, j)
  let l := Enriched.weightedCoend.face0 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j
  let r := Enriched.weightedCoend.face1 (EnrichedDayKernel.weight T p.2) (F1.externalTensor F2) i j
  let gi := EnrichedDayKernel.Output.actionGenerator T F1 F2 p.2 q.2 i
  let gj := EnrichedDayKernel.Output.actionGenerator T F1 F2 p.2 q.2 j
  let b := coefficientAction H p q
  have hi :
      (R ⊗ S) ◁ (B ◁ l) ≫
          tensorμ R S B (EnrichedDayKernel.objects T F1 F2 p.2 i) ≫ (b ⊗ₘ gi) =
        tensorμ R S B Z ≫ (b ⊗ₘ (S ◁ l ≫ gi)) := by
    have h := tensorμ_natural_right_assoc R S (𝟙 B) l (b ⊗ₘ gi)
    rw [tensorHom_comp_tensorHom] at h
    simpa only [Category.id_comp, id_tensorHom, MonoidalCategory.whiskerLeft_id] using h
  have hj :
      (R ⊗ S) ◁ (B ◁ r) ≫
          tensorμ R S B (EnrichedDayKernel.objects T F1 F2 p.2 j) ≫ (b ⊗ₘ gj) =
        tensorμ R S B Z ≫ (b ⊗ₘ (S ◁ r ≫ gj)) := by
    have h := tensorμ_natural_right_assoc R S (𝟙 B) r (b ⊗ₘ gj)
    rw [tensorHom_comp_tensorHom] at h
    simpa only [Category.id_comp, id_tensorHom, MonoidalCategory.whiskerLeft_id] using h
  have hb : S ◁ l ≫ gi = S ◁ r ≫ gj := Left.innerAction_balanced T F1 F2 p.2 q.2 i j
  rw [a1_innerGenerator, a1_innerGenerator]
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  change Wq ◁ ((R ⊗ S) ◁ (B ◁ l)) ≫
      Wq ◁ (tensorμ R S B (EnrichedDayKernel.objects T F1 F2 p.2 i) ≫ (b ⊗ₘ gi)) =
    Wq ◁ ((R ⊗ S) ◁ (B ◁ r)) ≫
      Wq ◁ (tensorμ R S B (EnrichedDayKernel.objects T F1 F2 p.2 j) ≫ (b ⊗ₘ gj))
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
    hi, hj, hb]

section InnerQuotient

variable (p : E × K)
  [HasCoproduct (objects T U F1 F2 H m p)]
  [HasCoproduct (innerRelations T U F1 F2 H m p)]

/-- The coproduct map of the original inner weight faces in the right object family. -/
abbrev innerLeftMap := Enriched.weightedCoend.Mapped.mappedLeftMap (EnrichedDayKernel.weight T p.2)
  (F1.externalTensor F2) (objectFunctor U H m p)

/-- The coproduct map of the original inner diagram-action faces in the right object family. -/
abbrev innerRightMap :=
  Enriched.weightedCoend.Mapped.mappedRightMap (EnrichedDayKernel.weight T p.2)
  (F1.externalTensor F2) (objectFunctor U H m p)

variable [HasCoequalizer (innerLeftMap T U F1 F2 H m p)
  (innerRightMap T U F1 F2 H m p)]

/-- The chosen coequalizer of the original right inner relation coproduct maps. -/
abbrev innerPoint := coequalizer (innerLeftMap T U F1 F2 H m p)
  (innerRightMap T U F1 F2 H m p)

/-- The actual chosen right inner coequalizer projection on each original object summand. -/
abbrev innerProjection (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶ innerPoint T U F1 F2 H m p :=
  Sigma.ι (objects T U F1 F2 H m p) i ≫
    coequalizer.π (innerLeftMap T U F1 F2 H m p) (innerRightMap T U F1 F2 H m p)

variable [HasCoproduct (EnrichedDayKernel.objects T F1 F2 p.2)]
  [HasCoproduct (EnrichedDayKernel.relations T F1 F2 p.2)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 p.2)
    (EnrichedDayKernel.rightMap T F1 F2 p.2)]

/-- The canonical comparison from the right inner quotient to its actual tensor-preserved coend. -/
@[no_expose]
def innerIso : innerPoint T U F1 F2 H m p ≅
    (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.2) :=
  Enriched.weightedCoend.Mapped.mappedQuotientIso (EnrichedDayKernel.weight T p.2)
    (F1.externalTensor F2) (objectFunctor U H m p)

@[reassoc]
theorem innerProjection_iso (i : C1 × C2) :
    innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom =
      innerGenerator T U F1 F2 H m p i :=
  Enriched.weightedCoend.Mapped.mappedQuotientIso_generator (EnrichedDayKernel.weight T p.2)
    (F1.externalTensor F2) (objectFunctor U H m p) i

theorem outerFace0_innerProjection (q : E × K) (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerProjection T U F1 F2 H m p i =
      r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerProjection T U F1 F2 H m p j := by
  apply (cancel_mono (innerIso T U F1 F2 H m p).hom).1
  calc
    _ = r0 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m p i := by
      rw [Category.assoc, Category.assoc, innerProjection_iso]
    _ = r1 T U F1 F2 H m p q i j ≫ a0 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m p j := outerFace0_innerGenerator T U F1 F2 H m p q i j
    _ = _ := by
      symm
      rw [Category.assoc, Category.assoc, innerProjection_iso]

end InnerQuotient

theorem outerFace1_innerProjection (p q : E × K)
    [HasCoproduct (objects T U F1 F2 H m q)]
    [HasCoproduct (innerRelations T U F1 F2 H m q)]
    [HasCoequalizer (innerLeftMap T U F1 F2 H m q) (innerRightMap T U F1 F2 H m q)]
    [HasCoproduct (EnrichedDayKernel.objects T F1 F2 q.2)]
    [HasCoproduct (EnrichedDayKernel.relations T F1 F2 q.2)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 q.2)
      (EnrichedDayKernel.rightMap T F1 F2 q.2)] (i j : C1 × C2) :
    r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerProjection T U F1 F2 H m q i =
      r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerProjection T U F1 F2 H m q j := by
  apply (cancel_mono (innerIso T U F1 F2 H m q).hom).1
  calc
    _ = r0 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q i ≫
        innerGenerator T U F1 F2 H m q i := by
      rw [Category.assoc, Category.assoc, innerProjection_iso]
    _ = r1 T U F1 F2 H m p q i j ≫ a1 T U F1 F2 H m p q j ≫
        innerGenerator T U F1 F2 H m q j := outerFace1_innerGenerator T U F1 F2 H m p q i j
    _ = _ := by
      symm
      rw [Category.assoc, Category.assoc, innerProjection_iso]

section OriginalOuterFaces

variable [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]

/-- The actual right parent diagram: H tensored with the original inner kernel output functor. -/
abbrev originalOuterDiagram := H.externalTensor (EnrichedDayKernel.Output.functor T F1 F2)

/-- Map each original inner generator into the complete original right parent relation word. -/
abbrev relationGenerator (p q : E × K) (i : C1 × C2) :
    outerRelations T U F1 F2 H m p q i ⟶
      Enriched.weightedCoend.relations (EnrichedDayKernel.weight U m)
        (originalOuterDiagram T F1 F2 H) (p, q) :=
  (relationFunctor U H m p q).map (EnrichedDayKernel.gen T F1 F2 p.2 i)

theorem originalOuterFace0 (p q : E × K) (i : C1 × C2) :
    relationGenerator T U F1 F2 H m p q i ≫
        Enriched.weightedCoend.face0 (EnrichedDayKernel.weight U m)
          (originalOuterDiagram T F1 F2 H) p q =
      a0 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m p i :=
  (face0Transformation U H m p q).naturality (EnrichedDayKernel.gen T F1 F2 p.2 i)

theorem originalOuterFace1 (p q : E × K) (i : C1 × C2) :
    relationGenerator T U F1 F2 H m p q i ≫
        Enriched.weightedCoend.face1 (EnrichedDayKernel.weight U m)
          (originalOuterDiagram T F1 F2 H) p q =
      a1 T U F1 F2 H m p q i ≫ innerGenerator T U F1 F2 H m q i := by
  rw [a1_innerGenerator]
  simp only [Enriched.weightedCoend.face1, EnrichedFunctor.externalTensor_uncurry]
  let Wq := (EnrichedDayKernel.weight U m).obj (op q)
  let R := p.1 ⟶[V] q.1
  let S := p.2 ⟶[V] q.2
  let B := H.obj p.1
  let X := EnrichedDayKernel.objects T F1 F2 p.2 i
  let Q := EnrichedDayKernel.obj T F1 F2 p.2
  let g : X ⟶ Q := EnrichedDayKernel.gen T F1 F2 p.2 i
  let a := MonoidalClosed.uncurry (H.map p.1 q.1)
  let b := MonoidalClosed.uncurry (EnrichedDayKernel.Output.map T F1 F2 p.2 q.2)
  change Wq ◁ ((R ⊗ S) ◁ (B ◁ g)) ≫
      Wq ◁ ((β_ (R ⊗ S) (B ⊗ Q)).hom ≫ tensorμ B Q R S ≫ (a ⊗ₘ b)) =
    Wq ◁ (tensorμ R S B X ≫
      (((β_ R B).hom ≫ a) ⊗ₘ
        EnrichedDayKernel.Output.actionGenerator T F1 F2 p.2 q.2 i))
  rw [← MonoidalCategory.whiskerLeft_comp]
  have h := tensorActionWord R S (𝟙 B) g a b
  simp only [id_tensorHom, MonoidalCategory.id_whiskerRight, Category.id_comp] at h
  have hn := EnrichedDayKernel.Output.gen_naturality T F1 F2 p.2 q.2 i
  simp only [tensorHom_id] at hn
  rw [hn] at h
  exact congrArg (fun f => Wq ◁ f) h

section NestedGenerator

variable [HasCoproduct (EnrichedDayKernel.objects U H
    (EnrichedDayKernel.Output.functor T F1 F2) m)]
  [HasCoproduct (EnrichedDayKernel.relations U H
    (EnrichedDayKernel.Output.functor T F1 F2) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U H
    (EnrichedDayKernel.Output.functor T F1 F2) m)
    (EnrichedDayKernel.rightMap U H (EnrichedDayKernel.Output.functor T F1 F2) m)]

/-- The full original right-nested Day generator, including both original coend legs. -/
abbrev nestedGenerator (p : E × K) (i : C1 × C2) :
    objects T U F1 F2 H m p i ⟶
      EnrichedDayKernel.obj U H (EnrichedDayKernel.Output.functor T F1 F2) m :=
  innerGenerator T U F1 F2 H m p i ≫
    EnrichedDayKernel.gen U H (EnrichedDayKernel.Output.functor T F1 F2) m p

theorem nestedGenerator_innerProjection (p : E × K)
    [HasCoproduct (objects T U F1 F2 H m p)]
    [HasCoproduct (innerRelations T U F1 F2 H m p)]
    [HasCoequalizer (innerLeftMap T U F1 F2 H m p) (innerRightMap T U F1 F2 H m p)]
    (i : C1 × C2) :
    innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom ≫
        EnrichedDayKernel.gen U H (EnrichedDayKernel.Output.functor T F1 F2) m p =
      nestedGenerator T U F1 F2 H m p i := by
  let g : (objectFunctor U H m p).obj (EnrichedDayKernel.obj T F1 F2 p.2) ⟶
      EnrichedDayKernel.obj U H (EnrichedDayKernel.Output.functor T F1 F2) m :=
    EnrichedDayKernel.gen U H (EnrichedDayKernel.Output.functor T F1 F2) m p
  change innerProjection T U F1 F2 H m p i ≫ (innerIso T U F1 F2 H m p).hom ≫ g =
    innerGenerator T U F1 F2 H m p i ≫ g
  rw [← Category.assoc, innerProjection_iso]

end NestedGenerator

end OriginalOuterFaces

end Right
end RightNested

section NativeIndex

universe uI vI
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  (F G H : EnrichedFunctor V I V) (m : I)

attribute [local instance] Enriched.prodCategory

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [∀ p : I × I, HasCoproduct
    (Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoproduct
    (Left.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoequalizer
    (Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
    (Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoproduct
    (Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoproduct
    (Right.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoequalizer
    (Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
    (Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G) H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G H) m)]

/-- Both original nested Day presentations have all four full-Hom face equations,
and their chosen inner projections retain the original whole nested generator legs. -/
theorem bothNestedFaces (p q : I × I) (i j : I × I) :
    (Left.r0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i j ≫
        Left.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i ≫
        Left.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p i =
      Left.r1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i j ≫
        Left.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q j ≫
        Left.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p j) ∧
    (Left.r0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i j ≫
        Left.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i ≫
        Left.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m q i =
      Left.r1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q i j ≫
        Left.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p q j ≫
        Left.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m q j) ∧
    (Right.r0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i j ≫
        Right.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i ≫
        Right.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p i =
      Right.r1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i j ≫
        Right.a0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q j ≫
        Right.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p j) ∧
    (Right.r0 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i j ≫
        Right.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i ≫
        Right.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m q i =
      Right.r1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q i j ≫
        Right.a1 d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p q j ≫
        Right.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m q j) ∧
    (Left.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p i ≫
        (Left.innerIso d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p).hom ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G) H m p =
      Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p i) ∧
    (Right.innerProjection d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p i ≫
        (Right.innerIso d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p).hom ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor F
          (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G H) m p =
      Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p i) := by
  exact ⟨Left.outerFace0_innerProjection _ _ _ _ _ _ p q i j,
    Left.outerFace1_innerProjection _ _ _ _ _ _ p q i j,
    Right.outerFace0_innerProjection _ _ _ _ _ _ p q i j,
    Right.outerFace1_innerProjection _ _ _ _ _ _ p q i j,
    Left.nestedGenerator_innerProjection _ _ _ _ _ _ p i,
    Right.nestedGenerator_innerProjection _ _ _ _ _ _ p i⟩

end NativeIndex

end CategoryTheory.EnrichedDayKernel.AssociatorFaces
