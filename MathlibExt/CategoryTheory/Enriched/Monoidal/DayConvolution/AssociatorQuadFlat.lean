/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadCoefficients

/-!
# Associator Quad Flat

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadFlat
/-- The five parenthesizations of four inputs occurring in the associator pentagon. -/
inductive Bracket where
  | a | b | c | d | e
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed
  V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  (F G H J : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
/-- The full four-input product `((I × I) × I) × I` for every flat pentagon vertex. -/
abbrev indices := ((I × I) × I) × I
/-- The five original full enriched index words, on the unchanged four-input product. -/
abbrev index (q : Bracket) : EnrichedFunctor V (indices (I := I)) I :=
  match q with
  | .a => AssociatorQuadIndex.indexA d
  | .b => AssociatorQuadIndex.indexB d
  | .c => AssociatorQuadIndex.indexC d
  | .d => AssociatorQuadIndex.indexD d
  | .e => AssociatorQuadIndex.indexE d
/-- The five original ordered coefficient words and complete four-input Hom actions. -/
abbrev coefficient (q : Bracket) : EnrichedFunctor V (indices (I := I)) V :=
  match q with
  | .a => AssociatorQuadCoefficient.coefficientA F G H J
  | .b => AssociatorQuadCoefficient.coefficientB F G H J
  | .c => AssociatorQuadCoefficient.coefficientC F G H J
  | .d => AssociatorQuadCoefficient.coefficientD F G H J
  | .e => AssociatorQuadCoefficient.coefficientE F G H J
/-- The represented weight at `m` for the index tensor of the selected bracket. -/
abbrev weight (q : Bracket) : EnrichedFunctor V (indices (I := I))ᵒᵖ V := EnrichedDayKernel.weight
  (index d q) m
/-- The object summands of the weighted coend for the selected pentagon bracket. -/
abbrev objects (q : Bracket) : indices (I := I) → V := Enriched.weightedCoend.objects (weight d m q)
  (coefficient F G H J q)
/-- The relation summands of the weighted coend for the selected pentagon bracket. -/
abbrev relations (q : Bracket) : indices (I := I) × indices (I := I) → V :=
  Enriched.weightedCoend.relations (weight d m q) (coefficient F G H J q)
section Choices
variable [∀ q : Bracket, HasCoproduct (objects d F G H J m q)]
  [∀ q : Bracket, HasCoproduct (relations d F G H J m q)]
/-- The relation map induced by the contravariant weight action at the selected bracket. -/
abbrev map0 (q : Bracket) := Enriched.weightedCoend.leftMap (weight d m q) (coefficient F G H J q)
/-- The relation map induced by the covariant coefficient action at the selected bracket. -/
abbrev map1 (q : Bracket) := Enriched.weightedCoend.rightMap (weight d m q) (coefficient F G H J q)
variable [∀ q : Bracket, HasCoequalizer (map0 d F G H J m q) (map1 d F G H J m q)]
/-- The chosen flat weighted coend at the selected pentagon vertex. -/
abbrev point (q : Bracket) : V := Enriched.weightedCoend (weight d m q) (coefficient F G H J q)
/-- The canonical map from a four-input object summand to the selected flat pentagon
  coend. -/
abbrev generator (q : Bracket) (X : indices (I := I)) : objects d F G H J m q X ⟶ point d F G H J m
  q :=
  Enriched.weightedCoend.ι (weight d m q) (coefficient F G H J q) X
end Choices

/-- The AB weight map is precomposition by the actual inverse index associator. -/
abbrev weightIsoAB (X : indices (I := I)) : (weight d m .a).obj (op X) ≅ (weight d m .b).obj (op X)
  :=
  AssociatorQuadMaps.weightIso (AssociatorQuadIndex.indexA d) (AssociatorQuadIndex.indexB d)
    (AssociatorQuadIndex.edgeAB d) m X
/-- AB preserves the complete original four-input weight action. -/
@[reassoc]
theorem weightAB_naturality (X Y : indices (I := I)) :
    MonoidalClosed.uncurry ((weight d m .a).map (op Y) (op X)) ≫ (weightIsoAB d m X).hom =
      ((weightIsoAB d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight d m .b).map (op Y) (op X)) :=
  AssociatorQuadMaps.weight_naturality (AssociatorQuadIndex.indexA d) (AssociatorQuadIndex.indexB d)
    (AssociatorQuadIndex.edgeAB d) (AssociatorQuadIndex.edgeAB_map d) m X Y

/-- The BC weight map is precomposition by the actual inverse index associator. -/
abbrev weightIsoBC (X : indices (I := I)) : (weight d m .b).obj (op X) ≅ (weight d m .c).obj (op X)
  :=
  AssociatorQuadMaps.weightIso (AssociatorQuadIndex.indexB d) (AssociatorQuadIndex.indexC d)
    (AssociatorQuadIndex.edgeBC d) m X
/-- BC preserves the complete original four-input weight action. -/
@[reassoc]
theorem weightBC_naturality (X Y : indices (I := I)) :
    MonoidalClosed.uncurry ((weight d m .b).map (op Y) (op X)) ≫ (weightIsoBC d m X).hom =
      ((weightIsoBC d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight d m .c).map (op Y) (op X)) :=
  AssociatorQuadMaps.weight_naturality (AssociatorQuadIndex.indexB d) (AssociatorQuadIndex.indexC d)
    (AssociatorQuadIndex.edgeBC d) (AssociatorQuadIndex.edgeBC_map d) m X Y

/-- The AD weight map is precomposition by the actual inverse index associator. -/
abbrev weightIsoAD (X : indices (I := I)) : (weight d m .a).obj (op X) ≅ (weight d m .d).obj (op X)
  :=
  AssociatorQuadMaps.weightIso (AssociatorQuadIndex.indexA d) (AssociatorQuadIndex.indexD d)
    (AssociatorQuadIndex.edgeAD d) m X
/-- AD preserves the complete original four-input weight action. -/
@[reassoc]
theorem weightAD_naturality (X Y : indices (I := I)) :
    MonoidalClosed.uncurry ((weight d m .a).map (op Y) (op X)) ≫ (weightIsoAD d m X).hom =
      ((weightIsoAD d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight d m .d).map (op Y) (op X)) :=
  AssociatorQuadMaps.weight_naturality (AssociatorQuadIndex.indexA d) (AssociatorQuadIndex.indexD d)
    (AssociatorQuadIndex.edgeAD d) (AssociatorQuadIndex.edgeAD_map d) m X Y

/-- The DE weight map is precomposition by the actual inverse index associator. -/
abbrev weightIsoDE (X : indices (I := I)) : (weight d m .d).obj (op X) ≅ (weight d m .e).obj (op X)
  :=
  AssociatorQuadMaps.weightIso (AssociatorQuadIndex.indexD d) (AssociatorQuadIndex.indexE d)
    (AssociatorQuadIndex.edgeDE d) m X
/-- DE preserves the complete original four-input weight action. -/
@[reassoc]
theorem weightDE_naturality (X Y : indices (I := I)) :
    MonoidalClosed.uncurry ((weight d m .d).map (op Y) (op X)) ≫ (weightIsoDE d m X).hom =
      ((weightIsoDE d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight d m .e).map (op Y) (op X)) :=
  AssociatorQuadMaps.weight_naturality (AssociatorQuadIndex.indexD d) (AssociatorQuadIndex.indexE d)
    (AssociatorQuadIndex.edgeDE d) (AssociatorQuadIndex.edgeDE_map d) m X Y

/-- The EC weight map is precomposition by the actual inverse index associator. -/
abbrev weightIsoEC (X : indices (I := I)) : (weight d m .e).obj (op X) ≅ (weight d m .c).obj (op X)
  :=
  AssociatorQuadMaps.weightIso (AssociatorQuadIndex.indexE d) (AssociatorQuadIndex.indexC d)
    (AssociatorQuadIndex.edgeEC d) m X
/-- EC preserves the complete original four-input weight action. -/
@[reassoc]
theorem weightEC_naturality (X Y : indices (I := I)) :
    MonoidalClosed.uncurry ((weight d m .e).map (op Y) (op X)) ≫ (weightIsoEC d m X).hom =
      ((weightIsoEC d m Y).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((weight d m .c).map (op Y) (op X)) :=
  AssociatorQuadMaps.weight_naturality (AssociatorQuadIndex.indexE d) (AssociatorQuadIndex.indexC d)
    (AssociatorQuadIndex.edgeEC d) (AssociatorQuadIndex.edgeEC_map d) m X Y

section Edges
variable [∀ q : Bracket, HasCoproduct (objects d F G H J m q)]
  [∀ q : Bracket, HasCoproduct (relations d F G H J m q)]
  [∀ q : Bracket, HasCoequalizer (map0 d F G H J m q) (map1 d F G H J m q)]

/-- The actual AB comparison of the two original chosen four-input coends. -/
def edgeAB : point d F G H J m .a ≅ point d F G H J m .b :=
  Enriched.weightedCoend.ComponentIso.iso (weight d m .a) (weight d m .b)
    (coefficient F G H J .a) (coefficient F G H J
    .b)
    (weightIsoAB d m) (AssociatorQuadCoefficient.edgeAB F G H J)
    (weightAB_naturality d m) (AssociatorQuadCoefficient.edgeAB_naturality F G H J)

/-- The AB hom retains every original generator and both actual factors. -/
@[reassoc]
theorem generator_edgeAB_hom (X : indices (I := I)) :
    generator d F G H J m .a X ≫ (edgeAB d F G H J m).hom =
      ((weightIsoAB d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAB F G H J X).hom) ≫
        generator d F G H J m .b X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_hom (weight d m .a) (weight d m .b)
    (coefficient F G H J .a) (coefficient F
    G H J .b)
    (weightIsoAB d m) (AssociatorQuadCoefficient.edgeAB F G H J)
    (weightAB_naturality d m) (AssociatorQuadCoefficient.edgeAB_naturality F G H J) X

/-- The AB inverse retains the same original generator and both opposite factors. -/
@[reassoc]
theorem generator_edgeAB_inv (X : indices (I := I)) :
    generator d F G H J m .b X ≫ (edgeAB d F G H J m).inv =
      ((weightIsoAB d m X).inv ⊗ₘ (AssociatorQuadCoefficient.edgeAB F G H J X).inv) ≫
        generator d F G H J m .a X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_inv (weight d m .a) (weight d m .b)
    (coefficient F G H J .a) (coefficient F
    G H J .b)
    (weightIsoAB d m) (AssociatorQuadCoefficient.edgeAB F G H J)
    (weightAB_naturality d m) (AssociatorQuadCoefficient.edgeAB_naturality F G H J) X

/-- The actual BC comparison of the two original chosen four-input coends. -/
def edgeBC : point d F G H J m .b ≅ point d F G H J m .c :=
  Enriched.weightedCoend.ComponentIso.iso (weight d m .b) (weight d m .c)
    (coefficient F G H J .b) (coefficient F G H J
    .c)
    (weightIsoBC d m) (AssociatorQuadCoefficient.edgeBC F G H J)
    (weightBC_naturality d m) (AssociatorQuadCoefficient.edgeBC_naturality F G H J)

/-- The BC hom retains every original generator and both actual factors. -/
@[reassoc]
theorem generator_edgeBC_hom (X : indices (I := I)) :
    generator d F G H J m .b X ≫ (edgeBC d F G H J m).hom =
      ((weightIsoBC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeBC F G H J X).hom) ≫
        generator d F G H J m .c X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_hom (weight d m .b) (weight d m .c)
    (coefficient F G H J .b) (coefficient F
    G H J .c)
    (weightIsoBC d m) (AssociatorQuadCoefficient.edgeBC F G H J)
    (weightBC_naturality d m) (AssociatorQuadCoefficient.edgeBC_naturality F G H J) X

/-- The BC inverse retains the same original generator and both opposite factors. -/
@[reassoc]
theorem generator_edgeBC_inv (X : indices (I := I)) :
    generator d F G H J m .c X ≫ (edgeBC d F G H J m).inv =
      ((weightIsoBC d m X).inv ⊗ₘ (AssociatorQuadCoefficient.edgeBC F G H J X).inv) ≫
        generator d F G H J m .b X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_inv (weight d m .b) (weight d m .c)
    (coefficient F G H J .b) (coefficient F
    G H J .c)
    (weightIsoBC d m) (AssociatorQuadCoefficient.edgeBC F G H J)
    (weightBC_naturality d m) (AssociatorQuadCoefficient.edgeBC_naturality F G H J) X

/-- The actual AD comparison of the two original chosen four-input coends. -/
def edgeAD : point d F G H J m .a ≅ point d F G H J m .d :=
  Enriched.weightedCoend.ComponentIso.iso (weight d m .a) (weight d m .d)
    (coefficient F G H J .a) (coefficient F G H J
    .d)
    (weightIsoAD d m) (AssociatorQuadCoefficient.edgeAD F G H J)
    (weightAD_naturality d m) (AssociatorQuadCoefficient.edgeAD_naturality F G H J)

/-- The AD hom retains every original generator and both actual factors. -/
@[reassoc]
theorem generator_edgeAD_hom (X : indices (I := I)) :
    generator d F G H J m .a X ≫ (edgeAD d F G H J m).hom =
      ((weightIsoAD d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAD F G H J X).hom) ≫
        generator d F G H J m .d X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_hom (weight d m .a) (weight d m .d)
    (coefficient F G H J .a) (coefficient F
    G H J .d)
    (weightIsoAD d m) (AssociatorQuadCoefficient.edgeAD F G H J)
    (weightAD_naturality d m) (AssociatorQuadCoefficient.edgeAD_naturality F G H J) X

/-- The AD inverse retains the same original generator and both opposite factors. -/
@[reassoc]
theorem generator_edgeAD_inv (X : indices (I := I)) :
    generator d F G H J m .d X ≫ (edgeAD d F G H J m).inv =
      ((weightIsoAD d m X).inv ⊗ₘ (AssociatorQuadCoefficient.edgeAD F G H J X).inv) ≫
        generator d F G H J m .a X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_inv (weight d m .a) (weight d m .d)
    (coefficient F G H J .a) (coefficient F
    G H J .d)
    (weightIsoAD d m) (AssociatorQuadCoefficient.edgeAD F G H J)
    (weightAD_naturality d m) (AssociatorQuadCoefficient.edgeAD_naturality F G H J) X

/-- The actual DE comparison of the two original chosen four-input coends. -/
def edgeDE : point d F G H J m .d ≅ point d F G H J m .e :=
  Enriched.weightedCoend.ComponentIso.iso (weight d m .d) (weight d m .e)
    (coefficient F G H J .d) (coefficient F G H J
    .e)
    (weightIsoDE d m) (AssociatorQuadCoefficient.edgeDE F G H J)
    (weightDE_naturality d m) (AssociatorQuadCoefficient.edgeDE_naturality F G H J)

/-- The DE hom retains every original generator and both actual factors. -/
@[reassoc]
theorem generator_edgeDE_hom (X : indices (I := I)) :
    generator d F G H J m .d X ≫ (edgeDE d F G H J m).hom =
      ((weightIsoDE d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeDE F G H J X).hom) ≫
        generator d F G H J m .e X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_hom (weight d m .d) (weight d m .e)
    (coefficient F G H J .d) (coefficient F
    G H J .e)
    (weightIsoDE d m) (AssociatorQuadCoefficient.edgeDE F G H J)
    (weightDE_naturality d m) (AssociatorQuadCoefficient.edgeDE_naturality F G H J) X

/-- The DE inverse retains the same original generator and both opposite factors. -/
@[reassoc]
theorem generator_edgeDE_inv (X : indices (I := I)) :
    generator d F G H J m .e X ≫ (edgeDE d F G H J m).inv =
      ((weightIsoDE d m X).inv ⊗ₘ (AssociatorQuadCoefficient.edgeDE F G H J X).inv) ≫
        generator d F G H J m .d X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_inv (weight d m .d) (weight d m .e)
    (coefficient F G H J .d) (coefficient F
    G H J .e)
    (weightIsoDE d m) (AssociatorQuadCoefficient.edgeDE F G H J)
    (weightDE_naturality d m) (AssociatorQuadCoefficient.edgeDE_naturality F G H J) X

/-- The actual EC comparison of the two original chosen four-input coends. -/
def edgeEC : point d F G H J m .e ≅ point d F G H J m .c :=
  Enriched.weightedCoend.ComponentIso.iso (weight d m .e) (weight d m .c)
    (coefficient F G H J .e) (coefficient F G H J
    .c)
    (weightIsoEC d m) (AssociatorQuadCoefficient.edgeEC F G H J)
    (weightEC_naturality d m) (AssociatorQuadCoefficient.edgeEC_naturality F G H J)

/-- The EC hom retains every original generator and both actual factors. -/
@[reassoc]
theorem generator_edgeEC_hom (X : indices (I := I)) :
    generator d F G H J m .e X ≫ (edgeEC d F G H J m).hom =
      ((weightIsoEC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeEC F G H J X).hom) ≫
        generator d F G H J m .c X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_hom (weight d m .e) (weight d m .c)
    (coefficient F G H J .e) (coefficient F
    G H J .c)
    (weightIsoEC d m) (AssociatorQuadCoefficient.edgeEC F G H J)
    (weightEC_naturality d m) (AssociatorQuadCoefficient.edgeEC_naturality F G H J) X

/-- The EC inverse retains the same original generator and both opposite factors. -/
@[reassoc]
theorem generator_edgeEC_inv (X : indices (I := I)) :
    generator d F G H J m .c X ≫ (edgeEC d F G H J m).inv =
      ((weightIsoEC d m X).inv ⊗ₘ (AssociatorQuadCoefficient.edgeEC F G H J X).inv) ≫
        generator d F G H J m .e X :=
  Enriched.weightedCoend.ComponentIso.ι_iso_inv (weight d m .e) (weight d m .c)
    (coefficient F G H J .e) (coefficient F
    G H J .c)
    (weightIsoEC d m) (AssociatorQuadCoefficient.edgeEC F G H J)
    (weightEC_naturality d m) (AssociatorQuadCoefficient.edgeEC_naturality F G H J) X

end Edges

/-- Inverse index precomposition carries the actual index pentagon to the entire weight Hom. -/
theorem weight_pentagon (X : indices (I := I)) :
    (weightIsoAB d m X).hom ≫ (weightIsoBC d m X).hom =
      (weightIsoAD d m X).hom ≫ (weightIsoDE d m X).hom ≫ (weightIsoEC d m X).hom := by
  have he : (AssociatorQuadIndex.edgeAB d X) ≪≫ (AssociatorQuadIndex.edgeBC d X) =
      (AssociatorQuadIndex.edgeAD d X) ≪≫ (AssociatorQuadIndex.edgeDE d X) ≪≫
        (AssociatorQuadIndex.edgeEC d X) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Category.assoc] using AssociatorQuadIndex.edge_pentagon d X
  have hi := congrArg (fun z : (AssociatorQuadIndex.indexA d).obj X ≅
      (AssociatorQuadIndex.indexC d).obj X => z.inv) he
  simp only [Iso.trans_inv, Category.assoc] at hi
  have hw := congrArg (fun z => eHomWhiskerRight V z m) hi
  simp only [weightIsoAB, weightIsoBC, weightIsoAD, weightIsoDE, weightIsoEC,
    AssociatorQuadMaps.weightIso, Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id,
    Category.comp_id]
  change eHomWhiskerRight V (AssociatorQuadIndex.edgeAB d X).inv m ≫
      eHomWhiskerRight V (AssociatorQuadIndex.edgeBC d X).inv m =
    eHomWhiskerRight V (AssociatorQuadIndex.edgeAD d X).inv m ≫
      eHomWhiskerRight V (AssociatorQuadIndex.edgeDE d X).inv m ≫
      eHomWhiskerRight V (AssociatorQuadIndex.edgeEC d X).inv m
  simpa only [eHomWhiskerRight_comp, Category.assoc] using hw


section Pentagon
variable [∀ q : Bracket, HasCoproduct (objects d F G H J m q)]
  [∀ q : Bracket, HasCoproduct (relations d F G H J m q)]
  [∀ q : Bracket, HasCoequalizer (map0 d F G H J m q) (map1 d F G H J m q)]

/-- The pentagon on the five original chosen four-input coends follows on every actual generator. -/
theorem pentagon : (edgeAB d F G H J m).hom ≫ (edgeBC d F G H J m).hom =
    (edgeAD d F G H J m).hom ≫ (edgeDE d F G H J m).hom ≫ (edgeEC d F G H J m).hom := by
  apply Enriched.weightedCoend.hom_ext (weight d m .a) (coefficient F G H J .a)
  intro X
  let PA := point d F G H J m .a
  let WA := (weight d m .a).obj (op X)
  let CA := (coefficient F G H J .a).obj X
  let gA : WA ⊗ CA ⟶ PA := generator d F G H J m .a X
  let PB := point d F G H J m .b
  let WB := (weight d m .b).obj (op X)
  let CB := (coefficient F G H J .b).obj X
  let gB : WB ⊗ CB ⟶ PB := generator d F G H J m .b X
  let PC := point d F G H J m .c
  let WC := (weight d m .c).obj (op X)
  let CC := (coefficient F G H J .c).obj X
  let gC : WC ⊗ CC ⟶ PC := generator d F G H J m .c X
  let PD := point d F G H J m .d
  let WD := (weight d m .d).obj (op X)
  let CD := (coefficient F G H J .d).obj X
  let gD : WD ⊗ CD ⟶ PD := generator d F G H J m .d X
  let PE := point d F G H J m .e
  let WE := (weight d m .e).obj (op X)
  let CE := (coefficient F G H J .e).obj X
  let gE : WE ⊗ CE ⟶ PE := generator d F G H J m .e X
  let fAB : PA ⟶ PB := (edgeAB d F G H J m).hom
  let wAB : WA ⟶ WB := (weightIsoAB d m X).hom
  let cAB : CA ⟶ CB := (AssociatorQuadCoefficient.edgeAB F G H J X).hom
  have hAB : gA ≫ fAB = (wAB ⊗ₘ cAB) ≫ gB := generator_edgeAB_hom d F G H J m X
  let fBC : PB ⟶ PC := (edgeBC d F G H J m).hom
  let wBC : WB ⟶ WC := (weightIsoBC d m X).hom
  let cBC : CB ⟶ CC := (AssociatorQuadCoefficient.edgeBC F G H J X).hom
  have hBC : gB ≫ fBC = (wBC ⊗ₘ cBC) ≫ gC := generator_edgeBC_hom d F G H J m X
  let fAD : PA ⟶ PD := (edgeAD d F G H J m).hom
  let wAD : WA ⟶ WD := (weightIsoAD d m X).hom
  let cAD : CA ⟶ CD := (AssociatorQuadCoefficient.edgeAD F G H J X).hom
  have hAD : gA ≫ fAD = (wAD ⊗ₘ cAD) ≫ gD := generator_edgeAD_hom d F G H J m X
  let fDE : PD ⟶ PE := (edgeDE d F G H J m).hom
  let wDE : WD ⟶ WE := (weightIsoDE d m X).hom
  let cDE : CD ⟶ CE := (AssociatorQuadCoefficient.edgeDE F G H J X).hom
  have hDE : gD ≫ fDE = (wDE ⊗ₘ cDE) ≫ gE := generator_edgeDE_hom d F G H J m X
  let fEC : PE ⟶ PC := (edgeEC d F G H J m).hom
  let wEC : WE ⟶ WC := (weightIsoEC d m X).hom
  let cEC : CE ⟶ CC := (AssociatorQuadCoefficient.edgeEC F G H J X).hom
  have hEC : gE ≫ fEC = (wEC ⊗ₘ cEC) ≫ gC := generator_edgeEC_hom d F G H J m X
  have hl : gA ≫ fAB ≫ fBC = (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) ≫ gC := by
    rw [← Category.assoc, hAB, Category.assoc, hBC]
  have hr : gA ≫ fAD ≫ fDE ≫ fEC =
      (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) ≫ gC := by
    rw [← Category.assoc gA fAD, hAD, Category.assoc, ← Category.assoc gD fDE,
      hDE, Category.assoc, hEC]
  have hw : wAB ≫ wBC = wAD ≫ wDE ≫ wEC := weight_pentagon d m X
  have hc : cAB ≫ cBC = cAD ≫ cDE ≫ cEC := AssociatorQuadCoefficient.edge_pentagon F G H J X
  have ht : (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) = (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) := by
    simpa only [tensorHom_comp_tensorHom, Category.assoc] using
      congrArg₂ (fun w c => w ⊗ₘ c) hw hc
  have ht' : (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) ≫ gC =
      (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) ≫ gC := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ gC) ht
  change gA ≫ fAB ≫ fBC = gA ≫ fAD ≫ fDE ≫ fEC
  exact hl.trans (ht'.trans hr.symm)

end Pentagon
end CategoryTheory.EnrichedDayKernel.AssociatorQuadFlat
