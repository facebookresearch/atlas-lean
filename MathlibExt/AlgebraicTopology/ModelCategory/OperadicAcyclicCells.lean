/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure
public import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Closure
public import MathlibExt.CategoryTheory.Monoidal.EquivariantProfileCells
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Couniversal equivalences and compact generating sources

Cobase changes and filtered colimits retain the supplied whole arrows and
the caller's actual cocones. Relative compactness concerns the specified
cell class, including arbitrary coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w w' ν v u

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra

section WeakEquivalenceData

variable (C : Type u) [Category.{v} C] [CategoryWithWeakEquivalences C]

/-- Every actual cobase change of this whole arrow is a weak equivalence. -/
def couniversalWeakEquivalences : MorphismProperty C :=
  fun A B f => ∀ (X Y : C) (a : A ⟶ X) (q : X ⟶ Y) (b : B ⟶ Y),
    IsPushout a f q b → weakEquivalences C q

/-- Cobase change along this arrow, and along every cobase change of it,
preserves weak equivalences between the original objects under its source. -/
def hCofibrations : MorphismProperty C :=
  fun A B f => ∀ (X Y : C) (a : A ⟶ X) (q : X ⟶ Y) (b : B ⟶ Y),
    IsPushout a f q b → (weakEquivalences C).IsStableUnderCobaseChangeAlong q

/-- A genuine h-cofibration which is also a weak equivalence. -/
def acyclicHCofibrations : MorphismProperty C :=
  hCofibrations C ⊓ weakEquivalences C

variable {C}

/-- The identity cobase change recovers the unchanged original arrow. -/
theorem couniversalWeakEquivalences_le_weakEquivalences :
    couniversalWeakEquivalences C ≤ weakEquivalences C := by
  intro A B f hf
  exact hf A B (𝟙 A) f (𝟙 B) IsPushout.of_id_fst

/-- Pasting retains the actual arbitrary first and second cobase changes. -/
instance couniversalWeakEquivalences_isStableUnderCobaseChange :
    (couniversalWeakEquivalences C).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    intro X Y a q b st
    exact hf X Y (g ≫ a) q (g' ≫ b) (sq.paste_horiz st)

/-- The original two cobase-change squares paste to the same h-cofibration square. -/
instance hCofibrations_isStableUnderCobaseChange :
    (hCofibrations C).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    intro X Y a q b st
    exact hf X Y (g ≫ a) q (g' ≫ b) (sq.paste_horiz st)

end WeakEquivalenceData

section TwoOutOfThree

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A couniversal equivalence has the usual h-cofibration preservation property. -/
theorem couniversalWeakEquivalences_le_acyclicHCofibrations :
    couniversalWeakEquivalences C ≤ acyclicHCofibrations C := by
  intro A B f hf
  refine ⟨?_, couniversalWeakEquivalences_le_weakEquivalences f hf⟩
  intro X Y a q b sq
  constructor
  intro Z T r d g st hg
  have hq : weakEquivalences C q := hf X Y a q b sq
  have hr : weakEquivalences C r := hf Z T (a ≫ g) r (b ≫ d) (sq.paste_horiz st.flip)
  have hqr : weakEquivalences C (q ≫ d) := by
    rw [st.w]
    exact (weakEquivalences C).comp_mem _ _ hg hr
  exact (weakEquivalences C).of_precomp _ _ hq hqr

/-- In a left proper model category the usual acyclic h-cofibration condition
implies weakness of every actual cobase change. -/
theorem acyclicHCofibrations_le_couniversalWeakEquivalences [IsLeftProper C] :
    acyclicHCofibrations C ≤ couniversalWeakEquivalences C := by
  intro A B f hf X Y a q b sq
  let d := factorizationData (cofibrations C) (trivialFibrations C) a
  let i := d.i
  let p := d.p
  let _ : Cofibration i := (cofibration_iff _).2 d.hi
  let _ : WeakEquivalence f := (weakEquivalence_iff _).2 hf.2
  let s₀ := IsPushout.of_hasPushout i f
  have hq₀ : weakEquivalences C (pushout.inl i f) :=
    (weakEquivalence_iff _).1 (IsLeftProper.weakEquivalence_of_isPushout s₀)
  have sq' : IsPushout (i ≫ p) f q b := by
    simpa only [i, p, d.fac] using sq
  let comparison := s₀.desc (p ≫ q) b (by
    rw [← Category.assoc]
    exact sq'.w)
  have s₁ : IsPushout p (pushout.inl i f) q comparison :=
    IsPushout.of_left' sq' s₀
  have hpres := hf.1 d.Z (pushout i f) i (pushout.inl i f) (pushout.inr i f) s₀
  have hcomparison : weakEquivalences C comparison :=
    hpres.of_isPushout s₁.flip d.hp.2
  have hcomposite : weakEquivalences C (p ≫ q) := by
    rw [s₁.w]
    exact (weakEquivalences C).comp_mem _ _ hq₀ hcomparison
  exact (weakEquivalences C).of_precomp _ _ d.hp.2 hcomposite

/-- Both conventional formulations retain the same whole source and target arrows. -/
theorem acyclicHCofibrations_eq_couniversalWeakEquivalences [IsLeftProper C] :
    acyclicHCofibrations C = couniversalWeakEquivalences C :=
  le_antisymm acyclicHCofibrations_le_couniversalWeakEquivalences
    couniversalWeakEquivalences_le_acyclicHCofibrations

end TwoOutOfThree

section TransfiniteCobaseChange

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasPushouts C]
  [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]

/-- The first source alternative closes the actual couniversal maps under
every continuous transfinite composition in the specified stage universe. -/
theorem couniversalWeakEquivalences_isStableUnderTransfiniteComposition :
    (couniversalWeakEquivalences C).IsStableUnderTransfiniteComposition.{w} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ :=
    { le := by
        intro A B f hf X Y a q b sq
        obtain ⟨c⟩ := hf
        let d := c.cobaseChange a sq
        have h : (couniversalWeakEquivalences C).pushouts ≤ weakEquivalences C :=
          (pushouts_le (P := couniversalWeakEquivalences C)).trans
            couniversalWeakEquivalences_le_weakEquivalences
        exact (weakEquivalences C).transfiniteCompositionsOfShape_le J q
          (d.ofLE h).mem }

end TransfiniteCobaseChange

section StationaryFactorization

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Factor a whole original arrow by a cofibration and a trivial fibration;
an already trivial-fibrational arrow keeps its source and identity first map. -/
def stationaryCofibrationFactorization :
    FactorizationData (cofibrations C) (trivialFibrations C) := by
  classical
  exact fun {A} _ f => if hf : trivialFibrations C f then
    ⟨A, 𝟙 A, f, Category.id_comp f, (cofibrations C).id_mem A, hf⟩
  else factorizationData (cofibrations C) (trivialFibrations C) f

/-- At an already trivial-fibrational arrow the complete factor record is stationary. -/
theorem stationaryCofibrationFactorization_of_trivialFibration
    {A B : C} (f : A ⟶ B) (hf : trivialFibrations C f) :
    stationaryCofibrationFactorization f =
      ⟨A, 𝟙 A, f, Category.id_comp f, (cofibrations C).id_mem A, hf⟩ := by
  simp only [stationaryCofibrationFactorization, dite_eq_left hf]

/-- A weak original input makes its actual first factor a trivial cofibration. -/
theorem stationaryCofibrationFactorization_left_trivial
    {A B : C} (f : A ⟶ B) (hf : weakEquivalences C f) :
    trivialCofibrations C (stationaryCofibrationFactorization f).i := by
  refine ⟨(stationaryCofibrationFactorization f).hi, ?_⟩
  apply (weakEquivalences C).of_postcomp _ _
    (stationaryCofibrationFactorization f).hp.2
  simpa only [(stationaryCofibrationFactorization f).fac] using hf

end StationaryFactorization

section Nonsymmetric

open MonoidalCategory
open scoped MonoidalCategory

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- Conventional h-monoidality tests tensors with arbitrary objects, for both
cofibrations and trivial cofibrations. -/
structure HMonoidality : Prop where
  cofibration_tensor {A B : C} (f : A ⟶ B) (hf : cofibrations C f) (Y : C) :
    hCofibrations C (f ▷ Y)
  trivialCofibration_tensor {A B : C} (f : A ⟶ B)
    (hf : trivialCofibrations C f) (Y : C) : acyclicHCofibrations C (f ▷ Y)

variable {C}

/-- The actual right unitor identifies every ordinary cofibration with its
tensor by the unit; no cofibrancy of that unit is required. -/
theorem HMonoidality.cofibrations_le_hCofibrations (h : HMonoidality C) :
    cofibrations C ≤ hCofibrations C := by
  intro A B f hf
  let e : Arrow.mk (f ▷ 𝟙_ C) ≅ Arrow.mk f :=
    Arrow.isoMk (ρ_ A) (ρ_ B) (rightUnitor_naturality f).symm
  exact (arrow_mk_iso_iff (hCofibrations C) e).1 (h.cofibration_tensor f hf (𝟙_ C))

/-- Conventional h-monoidality supplies left properness of the original model. -/
theorem HMonoidality.isLeftProper (h : HMonoidality C) : IsLeftProper C where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations :=
    { isStableUnderCobaseChangeAlong := by
        intro A B f hf
        exact (h.cofibrations_le_hCofibrations f hf) A B (𝟙 A) f (𝟙 B)
          IsPushout.of_id_fst }

/-- The nonsymmetric tensor-word criterion produces the actual monoid axiom,
including arbitrary coproducts, cobase changes, and continuous transfinite composites. -/
theorem monoidAxiom_of_hMonoidality [SymmetricCategory C] [HasCoproducts.{w} C]
    (h : HMonoidality C)
    [(acyclicHCofibrations C).IsStableUnderTransfiniteComposition.{w}] :
    MonoidAxiom.{w} C := by
  let _ : IsLeftProper C := h.isLeftProper
  have hEq := acyclicHCofibrations_eq_couniversalWeakEquivalences (C := C)
  let _ : (acyclicHCofibrations C).IsStableUnderCobaseChange := by
    rw [hEq]
    infer_instance
  let _ : (acyclicHCofibrations C).IsStableUnderCoproducts.{w} :=
    isStableUnderCoproducts_of_cobase_transfinite (acyclicHCofibrations C)
  have ht : tensorTrivialCofibrationsRight C ≤ acyclicHCofibrations C :=
    (tensorTrivialCofibrationsRight_le_iff C (acyclicHCofibrations C)).2
      (fun f hf Y => h.trivialCofibration_tensor f hf Y)
  have hc : (coproducts.{w} (tensorTrivialCofibrationsRight C)).pushouts ≤
      acyclicHCofibrations C :=
    (pushouts_le_iff (P := coproducts.{w} (tensorTrivialCofibrationsRight C))).2
      ((coproducts_le_iff (P := tensorTrivialCofibrationsRight C)).2 ht)
  exact ⟨((transfiniteCompositions_monotone hc).trans
    (transfiniteCompositions_le (acyclicHCofibrations C))).trans inf_le_right⟩

end Nonsymmetric

end HomotopicalAlgebra

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Hom preserves every filtered colimit whose actual transition arrows lie
in the specified class. This is relative compactness, rather than smallness
at a larger regular cardinal. -/
def IsCompactRelativeTo (P : MorphismProperty C) (A : C) : Prop :=
  ∀ (K : Type w) [SmallCategory K] [IsFiltered K] (F : K ⥤ C),
    (∀ (i j : K) (f : i ⟶ j), P (F.map f)) →
      PreservesColimit F (coyoneda.obj (Opposite.op A))

/-- The actual generating cofibrations retain compact domains and codomains
relative to the same specified class of transition arrows. -/
structure CompactGeneratingSources (I P : MorphismProperty C) : Prop where
  domains (i : I.toSet) : IsCompactRelativeTo.{w} P i.1.left
  codomains (i : I.toSet) : IsCompactRelativeTo.{w} P i.1.right

/-- Compact generating domains and codomains preserve the full right
lifting property at the supplied filtered-colimit arrow. -/
theorem rlp_of_filtered_colimit
    (I : MorphismProperty C) {K : Type w} [SmallCategory K] [IsFiltered K]
    {F G : K ⥤ C} (p : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (hF : IsColimit cF) (hG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j : K, cF.ι.app j ≫ q = p.app j ≫ cG.ι.app j)
    (hp : ∀ j : K, I.rlp (p.app j))
    (hSource : ∀ i : I.toSet, PreservesColimit F (coyoneda.obj (Opposite.op i.1.left)))
    (hTargetSource : ∀ i : I.toSet, PreservesColimit G (coyoneda.obj (Opposite.op i.1.left)))
    (hTargetTarget : ∀ i : I.toSet, PreservesColimit G (coyoneda.obj (Opposite.op i.1.right))) :
    I.rlp q := by
  intro A B i hi
  constructor
  intro a b sq
  let label : I.toSet := ⟨Arrow.mk i, hi⟩
  let _ : PreservesColimit F (coyoneda.obj (Opposite.op A)) := hSource label
  let _ : PreservesColimit G (coyoneda.obj (Opposite.op A)) := hTargetSource label
  let _ : PreservesColimit G (coyoneda.obj (Opposite.op B)) := hTargetTarget label
  obtain ⟨j₁, a₁, ha₁⟩ := exists_hom_of_preservesColimit_coyoneda hF a
  obtain ⟨j₂, b₂, hb₂⟩ := exists_hom_of_preservesColimit_coyoneda hG b
  let k := IsFiltered.max j₁ j₂
  let aₖ : A ⟶ F.obj k := a₁ ≫ F.map (IsFiltered.leftToMax j₁ j₂)
  let bₖ : B ⟶ G.obj k := b₂ ≫ G.map (IsFiltered.rightToMax j₁ j₂)
  have haₖ : aₖ ≫ cF.ι.app k = a := by
    dsimp only [aₖ]
    rw [Category.assoc, cF.w, ha₁]
  have hbₖ : bₖ ≫ cG.ι.app k = b := by
    dsimp only [bₖ]
    rw [Category.assoc, cG.w, hb₂]
  have he : (aₖ ≫ p.app k) ≫ cG.ι.app k = (i ≫ bₖ) ≫ cG.ι.app k := by
    rw [Category.assoc, ← hq, ← Category.assoc, haₖ,
      Category.assoc, hbₖ]
    exact sq.w
  obtain ⟨j, t, ht⟩ := exists_eq_of_preservesColimit_coyoneda_self hG
    (aₖ ≫ p.app k) (i ≫ bₖ) he
  let aⱼ : A ⟶ F.obj j := aₖ ≫ F.map t
  let bⱼ : B ⟶ G.obj j := bₖ ≫ G.map t
  have st : CommSq aⱼ i (p.app j) bⱼ := ⟨by
    dsimp only [aⱼ, bⱼ]
    rw [Category.assoc, p.naturality, ← Category.assoc]
    simpa only [Category.assoc] using ht⟩
  let _ : HasLiftingProperty i (p.app j) := hp j i hi
  let lift := st.lift
  refine ⟨⟨lift ≫ cF.ι.app j, ?_, ?_⟩⟩
  · rw [← Category.assoc, st.fac_left]
    dsimp only [aⱼ]
    rw [Category.assoc, cF.w, haₖ]
  · rw [Category.assoc, hq, ← Category.assoc, st.fac_right]
    dsimp only [bⱼ]
    rw [Category.assoc, cG.w, hbₖ]

/-- Relative compactness, rather than a preservation outcome hypothesis,
supplies the three Hom comparisons for both original columns. -/
theorem rlp_of_filtered_colimit_of_compact
    {I P : MorphismProperty C} (h : CompactGeneratingSources.{w} I P)
    {K : Type w} [SmallCategory K] [IsFiltered K]
    {F G : K ⥤ C} (p : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (hF : IsColimit cF) (hG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j : K, cF.ι.app j ≫ q = p.app j ≫ cG.ι.app j)
    (hp : ∀ j : K, I.rlp (p.app j))
    (hFmaps : ∀ (i j : K) (f : i ⟶ j), P (F.map f))
    (hGmaps : ∀ (i j : K) (f : i ⟶ j), P (G.map f)) :
    I.rlp q :=
  rlp_of_filtered_colimit I p cF cG hF hG q hq hp
    (fun i => h.domains i K F hFmaps)
    (fun i => h.domains i K G hGmaps)
    (fun i => h.codomains i K G hGmaps)

end CategoryTheory.MorphismProperty

namespace CategoryTheory.OrdinalCofibrationSmoothing

open HomotopicalAlgebra

variable (O : Type w) [LinearOrder O] [WellFoundedLT O]

/-- The unchanged ordinal is an ordinary direct Reedy category, with its
original degree and genuine identity inverse arrows. -/
def ordinalReedy : CategoryTheory.ReedyStructure O O :=
  CategoryTheory.ReedyStructure.mk id ⊤ (identities O) inferInstance inferInstance
    (fun f _ => leOfHom f)
    (fun _ hf => by cases hf; exact le_rfl)
    (fun f _ h => ⟨h, Subsingleton.elim _ _⟩)
    (fun _ hf _ => by cases hf; exact ⟨rfl, rfl⟩)
    (fun {i} _ f => ReedyFactorization.mk i (𝟙 i) f (.mk i) trivial (Category.id_comp f))
    (by
      intro i j f a b
      rcases a with ⟨z, a, p, hp, ha, hpa⟩
      cases ha
      rcases b with ⟨z, b, q, hq, hb, hqb⟩
      cases hb
      have hp' : p = f := by simpa only [Category.id_comp] using hp
      have hq' : q = f := by simpa only [Category.id_comp] using hq
      subst p
      subst q
      rfl)

variable {O}

local instance directHomSubsingleton (a b : (ordinalReedy O).Direct) :
    Subsingleton (a ⟶ b) where
  allEq f g := WideSubcategory.hom_ext _ (Subsingleton.elim f.hom g.hom)

local instance latchingHomSubsingleton (j : O)
    (a b : (ordinalReedy O).Latching j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact Subsingleton.elim _ _

/-- A comparison of original ordinal sources determines its full latching triangle. -/
def latchingHom {j : O} {a b : (ordinalReedy O).Latching j}
    (h : (ordinalReedy O).latchingSource a ≤ (ordinalReedy O).latchingSource b) : a ⟶ b :=
  ObjectProperty.homMk (Over.homMk ⟨homOfLE h, trivial⟩ (Subsingleton.elim _ _))

/-- Forget only the redundant unique arrow into j, retaining the original source. -/
def latchingToPrefix (j : O) : (ordinalReedy O).Latching j ⥤ Set.Iio j where
  obj a := ⟨(ordinalReedy O).latchingSource a, a.property⟩
  map f := homOfLE (leOfHom ((ordinalReedy O).latchingComparison f))

/-- Every original strict-prefix source has its genuine original arrow into j. -/
def prefixToLatching (j : O) : Set.Iio j ⥤ (ordinalReedy O).Latching j where
  obj a := (ordinalReedy O).latchingMk (homOfLE a.2.le) trivial a.2
  map f := latchingHom (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The full actual latching category is the unchanged strict ordinal prefix. -/
def latchingPrefixEquivalence (j : O) : (ordinalReedy O).Latching j ≌ Set.Iio j where
  functor := latchingToPrefix j
  inverse := prefixToLatching j
  unitIso := NatIso.ofComponents (fun a =>
    { hom := latchingHom le_rfl
      inv := latchingHom le_rfl
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ })
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)

instance latchingToPrefix_isEquivalence (j : O) : (latchingToPrefix j).IsEquivalence :=
  (latchingPrefixEquivalence j).isEquivalence_functor

/-- Every original latching object and comparison remains the same original ordinal map. -/
theorem latchingToPrefix_comp_inclusion (j : O) :
    latchingToPrefix j ⋙ (Set.principalSegIio j).monotone.functor =
      (ordinalReedy O).latchingInclusion j := rfl

section Cocones

variable {C : Type u} [Category.{v} C] (F : O ⥤ C) (j : O)

/-- The actual prefix cocone retains all the original latching legs. -/
theorem prefixCocone_whisker_latching :
    ((Set.principalSegIio j).cocone F).whisker (latchingToPrefix j) =
      (ordinalReedy O).latchingCocone F j := rfl

/-- A true original prefix colimit supplies the true original latching colimit. -/
def latchingIsColimitOfPrefix
    (h : IsColimit ((Set.principalSegIio j).cocone F)) :
    IsColimit ((ordinalReedy O).latchingCocone F j) :=
  (Functor.Final.isColimitWhiskerEquiv (latchingToPrefix j)
    ((Set.principalSegIio j).cocone F)).symm h

/-- At a genuinely colimiting original latching cocone, its canonical map is an isomorphism. -/
theorem latchingMap_isIso_of_isColimit
    [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]
    (h : IsColimit ((ordinalReedy O).latchingCocone F j)) :
    IsIso (ReedyStructure.latchingMap (ordinalReedy O) F j) := by
  let e : colimit ((ordinalReedy O).latchingDiagram F j) ≅ F.obj j :=
    (colimit.isColimit ((ordinalReedy O).latchingDiagram F j)).coconePointUniqueUpToIso h
  have he : e.hom = ReedyStructure.latchingMap (ordinalReedy O) F j := by
    apply colimit.hom_ext
    intro a
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit ((ordinalReedy O).latchingDiagram F j)) h a).trans
      ((ordinalReedy O).latchingMap_ι F j a).symm
  rw [← he]
  exact e.isIso_hom

end Cocones

section CappedDiagram

variable {C : Type u} [Category.{v} C]

/-- Cap the original ordinal at i, keeping the entire original earlier prefix. -/
def cappedIndex (i : O) : O ⥤ O :=
  (show Monotone (fun j : O => min j i) from fun _ _ h => min_le_min_right i h).functor

/-- Compare the capped original diagram with the full original diagram. -/
def cappedComparison (i : O) (F : O ⥤ C) : cappedIndex i ⋙ F ⟶ F where
  app j := F.map (homOfLE (min_le_left j i))
  naturality j k f := by
    dsimp only [Functor.comp_map, cappedIndex, Monotone.functor]
    rw [← F.map_comp, ← F.map_comp]
    congr 1

/-- Once the cap lies strictly in the original prefix, that prefix cocone is a colimit. -/
def cappedPrefixIsColimit (i j : O) (hij : i < j) (F : O ⥤ C) :
    IsColimit ((Set.principalSegIio j).cocone (cappedIndex i ⋙ F)) := by
  let D := (Set.principalSegIio j).monotone.functor ⋙ cappedIndex i ⋙ F
  let a : Set.Iio j := ⟨i, hij⟩
  let _ : Nonempty (Set.Iio j) := ⟨a⟩
  have hD : D.IsEventuallyConstantFrom a := by
    intro b f
    have h : i ≤ b.1 := leOfHom f
    change IsIso (F.map (homOfLE (min_le_min_right i h)))
    have he : min i i = min b.1 i := by rw [min_self, min_eq_right h]
    let _ : IsIso (homOfLE (min_le_min_right i h)) :=
      ⟨⟨homOfLE (le_of_eq he.symm), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    infer_instance
  let _ : IsIso (((Set.principalSegIio j).cocone (cappedIndex i ⋙ F)).ι.app a) := by
    change IsIso (F.map (homOfLE (min_le_min_right i hij.le)))
    have he : min i i = min j i := by rw [min_self, min_eq_right hij.le]
    let _ : IsIso (homOfLE (min_le_min_right i hij.le)) :=
      ⟨⟨homOfLE (le_of_eq he.symm), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    infer_instance
  exact hD.isColimitOfIsIso _

omit [WellFoundedLT O] in
/-- The cap is the original identity comparison at every earlier ordinal stage. -/
theorem cappedComparison_app_isIso_of_le (i j : O) (hji : j ≤ i) (F : O ⥤ C) :
    IsIso ((cappedComparison i F).app j) := by
  change IsIso (F.map (homOfLE (min_le_left j i)))
  have he : min j i = j := min_eq_left hji
  let _ : IsIso (homOfLE (min_le_left j i)) :=
    ⟨⟨homOfLE (le_of_eq he.symm), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  infer_instance

/-- The cap's actual latching map is an isomorphism after the cap stage. -/
theorem capped_latchingMap_isIso
    [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]
    (i j : O) (hij : i < j) (F : O ⥤ C) :
    IsIso (ReedyStructure.latchingMap (ordinalReedy O) (cappedIndex i ⋙ F) j) :=
  latchingMap_isIso_of_isColimit (cappedIndex i ⋙ F) j
    (latchingIsColimitOfPrefix (cappedIndex i ⋙ F) j (cappedPrefixIsColimit i j hij F))

end CappedDiagram

section ConstantSource

attribute [local instance] IsFiltered.isConnected

variable [OrderBot O] {C : Type u} [Category.{v} C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]

/-- A nonempty original latching prefix of a constant source has its original source as colimit. -/
theorem constant_latchingMap_isIso (X : C) (j : O) (hj : ¬ IsMin j) :
    IsIso (ReedyStructure.latchingMap (ordinalReedy O) ((Functor.const O).obj X) j) := by
  let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, not_isMin_iff_bot_lt.mp hj⟩⟩
  let _ : IsConnected ((ordinalReedy O).Latching j) :=
    isConnected_of_equivalent (latchingPrefixEquivalence j).symm
  exact latchingMap_isIso_of_isColimit ((Functor.const O).obj X) j
    (isColimitConstCocone ((ordinalReedy O).Latching j) X)

end ConstantSource

section CofibrationMaps

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]

/-- Capping a diagram with cofibrational nonempty latching maps gives genuine
cofibration corners at every original stage, including the unchanged earlier prefix. -/
theorem cappedComparison_latching_cofibration (F : O ⥤ C)
    (hF : ∀ j : O, ¬ IsMin j →
      cofibrations C (ReedyStructure.latchingMap (ordinalReedy O) F j))
    (i j : O) :
    cofibrations C (ReedyStructure.latchingCorner (ordinalReedy O) (cappedComparison i F) j) := by
  let r := ordinalReedy O
  let p := cappedComparison i F
  by_cases hji : j ≤ i
  · let _ : IsIso (p.app j) := cappedComparison_app_isIso_of_le i j hji F
    let _ (a : r.Latching j) : IsIso ((r.latchingTransformation p j).app a) :=
      cappedComparison_app_isIso_of_le i (r.latchingSource a) (a.property.le.trans hji) F
    let _ : IsIso (r.latchingTransformation p j) := NatIso.isIso_of_isIso_app _
    let _ : IsIso (colimMap (r.latchingTransformation p j)) := inferInstance
    let k := pushout.inl (ReedyStructure.latchingMap r (cappedIndex i ⋙ F) j)
      (colimMap (r.latchingTransformation p j))
    let _ : IsIso k := inferInstance
    have hk : cofibrations C (k ≫ ReedyStructure.latchingCorner r p j) := by
      rw [ReedyStructure.latchingCorner_inl]
      exact mem_cofibrations (p.app j)
    exact ((cofibrations C).cancel_left_of_respectsIso k _).1 hk
  · have hij : i < j := lt_of_not_ge hji
    let _ : IsIso (ReedyStructure.latchingMap r (cappedIndex i ⋙ F) j) :=
      capped_latchingMap_isIso i j hij F
    let k := pushout.inr (ReedyStructure.latchingMap r (cappedIndex i ⋙ F) j)
      (colimMap (r.latchingTransformation p j))
    let _ : IsIso k := inferInstance
    have hk : cofibrations C (k ≫ ReedyStructure.latchingCorner r p j) := by
      rw [ReedyStructure.latchingCorner_inr]
      exact hF j (not_isMin_iff.mpr ⟨i, hij⟩)
    exact ((cofibrations C).cancel_left_of_respectsIso k _).1 hk

/-- Every original comparison map is a cofibration. The proof uses the
actual capped diagram and source Reedy lifting theorem, without assuming
pointwise cofibrations are closed under arbitrary filtered colimits. -/
theorem map_cofibration_of_nonempty_latching (F : O ⥤ C)
    (hF : ∀ j : O, ¬ IsMin j →
      cofibrations C (ReedyStructure.latchingMap (ordinalReedy O) F j))
    {i j : O} (hij : i ≤ j) : cofibrations C (F.map (homOfLE hij)) := by
  have h := HomotopicalAlgebra.ReedyModel.component_cofibration_of_latchingCorners
    (ordinalReedy O) (cappedComparison i F) (cappedComparison_latching_cofibration F hF i) j
  let e : Arrow.mk ((cappedComparison i F).app j) ≅ Arrow.mk (F.map (homOfLE hij)) :=
    Arrow.isoMk (F.mapIso (eqToIso (min_eq_right hij))) (Iso.refl _) (by
      change F.map (eqToHom (min_eq_right hij)) ≫ F.map (homOfLE hij) =
        F.map (homOfLE (min_le_left j i)) ≫ 𝟙 _
      rw [Category.comp_id, ← F.map_comp]
      congr 1)
  exact ((cofibrations C).arrow_mk_iso_iff e).1 h

end CofibrationMaps

section RootedDiagram

variable [OrderBot O] {C : Type u} [Category.{v} C]

/-- The whole original diagram arrow from its unchanged bottom object. -/
def rootedArrow (F : O ⥤ C) : Arrow (O ⥤ C) :=
  Arrow.mk (show (Functor.const O).obj (F.obj ⊥) ⟶ F from
    { app j := F.map (homOfLE (bot_le : ⊥ ≤ j))
      naturality i j f := by
        change 𝟙 (F.obj ⊥) ≫ F.map (homOfLE bot_le) =
          F.map (homOfLE bot_le) ≫ F.map f
        rw [Category.id_comp, ← F.map_comp]
        rfl })

omit [WellFoundedLT O] in
/-- The root component is the original identity. -/
theorem rootedArrow_hom_bot (F : O ⥤ C) : (rootedArrow F).hom.app ⊥ = 𝟙 (F.obj ⊥) :=
  F.map_id _

end RootedDiagram

section SmoothingProducer

variable [OrderBot O] {C : Type u} [Category.{v} C] [ModelCategory C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]
  [∀ k, HasLimitsOfShape ((ordinalReedy O).Matching k) C]

/-- The source model's stationary factory constructs the full original
rooted-diagram factor; no diagram model or factorization is supplied. -/
def smoothingFactor (F : O ⥤ C) :
    (ReedyStructure.latchingClass (ordinalReedy O) (cofibrations C)).MapFactorizationData
      (ReedyStructure.matchingClass (ordinalReedy O) (trivialFibrations C)) (rootedArrow F).hom :=
  ReedyStructure.DegreeFactorization.classifiedFactor (ordinalReedy O) (rootedArrow F).hom
    stationaryCofibrationFactorization

/-- Each original coefficient comparison is a genuine trivial fibration. -/
theorem smoothingFactor_comparison_trivialFibration (F : O ⥤ C) (j : O) :
    trivialFibrations C ((smoothingFactor F).p.app j) :=
  HomotopicalAlgebra.ReedyModel.component_trivialFibration_of_matchingCorners
    (ordinalReedy O) (smoothingFactor F).p (smoothingFactor F).hp j

/-- The actual nonempty latching map of the produced middle diagram is a cofibration. -/
theorem smoothingFactor_latching_cofibration (F : O ⥤ C) (j : O) (hj : ¬ IsMin j) :
    cofibrations C (ReedyStructure.latchingMap (ordinalReedy O) (smoothingFactor F).Z j) := by
  let r := ordinalReedy O
  let q := smoothingFactor F
  let _ : IsIso (ReedyStructure.latchingMap r ((Functor.const O).obj (F.obj ⊥)) j) :=
    constant_latchingMap_isIso (F.obj ⊥) j hj
  let k := pushout.inr (ReedyStructure.latchingMap r ((Functor.const O).obj (F.obj ⊥)) j)
    (colimMap (r.latchingTransformation q.i j))
  let _ : IsIso k := inferInstance
  have h : cofibrations C (k ≫ ReedyStructure.latchingCorner r q.i j) :=
    (cofibrations C).comp_mem _ _ (mem_cofibrations k) (q.hi j)
  have hk : k ≫ ReedyStructure.latchingCorner r q.i j = ReedyStructure.latchingMap r q.Z j :=
    ReedyStructure.latchingCorner_inr r q.i j
  exact hk ▸ h

/-- Every actual middle-diagram transition is a source cofibration. -/
theorem smoothingFactor_map_cofibration (F : O ⥤ C) {i j : O} (hij : i ≤ j) :
    cofibrations C ((smoothingFactor F).Z.map (homOfLE hij)) :=
  map_cofibration_of_nonempty_latching (smoothingFactor F).Z
    (smoothingFactor_latching_cofibration F) hij

/-- The whole lower middle diagram is the actual restriction of the full produced diagram. -/
theorem smoothingFactor_lower_middle (F : O ⥤ C) (j : O) :
    (ReedyStructure.DegreeFactorization.lowerAt (ordinalReedy O) (rootedArrow F).hom
      stationaryCofibrationFactorization j).Z =
      (ordinalReedy O).restrictBelow (smoothingFactor F).Z j := rfl

/-- The complete lower comparison is the original restricted whole comparison. -/
theorem smoothingFactor_lower_comparison (F : O ⥤ C) (j : O) :
    (ReedyStructure.DegreeFactorization.lowerAt (ordinalReedy O) (rootedArrow F).hom
      stationaryCofibrationFactorization j).p =
      Functor.whiskerLeft ((ordinalReedy O).belowObjects j).ι (smoothingFactor F).p := rfl

/-- The same actual lower-prefix record used by the stationary source factory. -/
abbrev smoothingLowerFactor (F : O ⥤ C) (j : O) :=
  ReedyStructure.DegreeFactorization.lowerAt (ordinalReedy O) (rootedArrow F).hom
    stationaryCofibrationFactorization j

local instance matchingIsEmpty (j : O) : IsEmpty ((ordinalReedy O).Matching j) where
  false a := (not_le_of_gt a.property) (leOfHom ((ordinalReedy O).matchingArrow a))

/-- On the empty original matching shape, the lower comparison is an actual isomorphism. -/
theorem coefficientMatchingComparison_isIso (F : O ⥤ C) (j : O) :
    IsIso (ReedyStructure.StageFactory.matchingP (ordinalReedy O) (rootedArrow F).hom
      (smoothingLowerFactor F j) j rfl) := by
  let r := ordinalReedy O
  let L := smoothingLowerFactor F j
  let p := Functor.whiskerLeft (r.matchingBelow j rfl) L.p
  let _ (a : r.Matching j) : IsIso (p.app a) := isEmptyElim a
  let _ : IsIso p := NatIso.isIso_of_isIso_app _
  change IsIso (limMap p)
  infer_instance

/-- The original coefficient source is the actual lower latching colimit,
through its canonical isomorphism after every nonminimal degree. -/
theorem coefficientSource_inr_isIso (F : O ⥤ C) (j : O) (hj : ¬ IsMin j) :
    IsIso (pushout.inr
      (ReedyStructure.latchingMap (ordinalReedy O) (rootedArrow F).left j)
      (ReedyStructure.StageFactory.latchingI (ordinalReedy O) (rootedArrow F).hom
        (smoothingLowerFactor F j) j rfl)) := by
  let _ : IsIso (ReedyStructure.latchingMap (ordinalReedy O) (rootedArrow F).left j) :=
    constant_latchingMap_isIso (F.obj ⊥) j hj
  infer_instance

/-- The original coefficient target retains the original ordinary target object. -/
theorem coefficientTarget_snd_isIso (F : O ⥤ C) (j : O) :
    IsIso (pullback.snd
      (ReedyStructure.StageFactory.matchingP (ordinalReedy O) (rootedArrow F).hom
        (smoothingLowerFactor F j) j rfl)
      (ReedyStructure.matchingMap (ordinalReedy O) F j)) := by
  exact (IsPullback.of_hasPullback _ _).isIso_snd_of_isIso
    (coefficientMatchingComparison_isIso F j)

/-- The actual coefficient arrow is trivial-fibrational whenever its
original lower-latching comparison is trivial-fibrational. -/
theorem coefficientMap_trivialFibration_of_latching
    (F : O ⥤ C) (j : O) (hj : ¬ IsMin j)
    (h : trivialFibrations C (ReedyStructure.StageFactory.latchingP (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl)) :
    trivialFibrations C (ReedyStructure.StageFactory.coefficientMap (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl) := by
  let r := ordinalReedy O
  let f := (rootedArrow F).hom
  let L := smoothingLowerFactor F j
  let a := pushout.inr (ReedyStructure.latchingMap r (rootedArrow F).left j)
    (ReedyStructure.StageFactory.latchingI r f L j rfl)
  let b := pullback.snd (ReedyStructure.StageFactory.matchingP r f L j rfl)
    (ReedyStructure.matchingMap r F j)
  let i := ReedyStructure.StageFactory.coefficientMap r f L j rfl
  let _ : IsIso a := coefficientSource_inr_isIso F j hj
  let _ : IsIso b := coefficientTarget_snd_isIso F j
  have he : a ≫ i ≫ b = ReedyStructure.StageFactory.latchingP r f L j rfl :=
    ReedyStructure.StageFactory.coefficientMap_inr_snd r f L j rfl
  have hcomp : trivialFibrations C (a ≫ i ≫ b) := he.symm ▸ h
  have hright : trivialFibrations C (i ≫ b) :=
    ((trivialFibrations C).cancel_left_of_respectsIso a _).1 hcomp
  have hb : IsIso b := coefficientTarget_snd_isIso F j
  exact (@MorphismProperty.cancel_right_of_respectsIso C _ (trivialFibrations C)
    inferInstance _ _ _ i b hb).1 hright

/-- At an already trivial-fibrational coefficient arrow, the complete
original latching corner is an isomorphism by the stationary source factory. -/
theorem smoothingFactor_latchingCorner_isIso_of_coefficient
    (F : O ⥤ C) (j : O)
    (h : trivialFibrations C (ReedyStructure.StageFactory.coefficientMap (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl)) :
    IsIso (ReedyStructure.latchingCorner (ordinalReedy O) (smoothingFactor F).i j) := by
  let r := ordinalReedy O
  let f := (rootedArrow F).hom
  let L := smoothingLowerFactor F j
  have hi : IsIso (ReedyStructure.StageFactory.coefficientFactor r f L
      stationaryCofibrationFactorization j rfl).i := by
    change IsIso (stationaryCofibrationFactorization
      (ReedyStructure.StageFactory.coefficientMap r f L j rfl)).i
    rw [stationaryCofibrationFactorization_of_trivialFibration _ h]
    infer_instance
  change isomorphisms C (ReedyStructure.latchingCorner r
    (ReedyStructure.DegreeFactorization.factor r f stationaryCofibrationFactorization).i j)
  apply ((isomorphisms C).arrow_mk_iso_iff
    (ReedyStructure.DegreeFactorization.factorLatchingArrowIso r f
      stationaryCofibrationFactorization j)).2
  rw [ReedyStructure.DegreeFactorization.prefixAt_eq_nextPrefix]
  exact ((isomorphisms C).arrow_mk_iso_iff
    (ReedyStructure.StageCorners.latchingArrowIsoNew r f L stationaryCofibrationFactorization
      (⟨j, le_rfl⟩ : r.Through j) rfl)).2 hi

/-- The stationary original latching corner keeps the actual prefix colimit. -/
theorem smoothingFactor_latchingMap_isIso_of_coefficient
    (F : O ⥤ C) (j : O) (hj : ¬ IsMin j)
    (h : trivialFibrations C (ReedyStructure.StageFactory.coefficientMap (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl)) :
    IsIso (ReedyStructure.latchingMap (ordinalReedy O) (smoothingFactor F).Z j) := by
  let r := ordinalReedy O
  let q := smoothingFactor F
  let k := pushout.inr (ReedyStructure.latchingMap r (rootedArrow F).left j)
    (colimMap (r.latchingTransformation q.i j))
  let _ : IsIso (ReedyStructure.latchingMap r (rootedArrow F).left j) :=
    constant_latchingMap_isIso (F.obj ⊥) j hj
  let _ : IsIso k := inferInstance
  let _ : IsIso (ReedyStructure.latchingCorner r q.i j) :=
    smoothingFactor_latchingCorner_isIso_of_coefficient F j h
  have hcomp : IsIso (k ≫ ReedyStructure.latchingCorner r q.i j) := inferInstance
  have he : k ≫ ReedyStructure.latchingCorner r q.i j = ReedyStructure.latchingMap r q.Z j :=
    ReedyStructure.latchingCorner_inr r q.i j
  exact he ▸ hcomp

end SmoothingProducer

section PrefixColimits

variable {C : Type u} [Category.{v} C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]

/-- An isomorphism from the original latching colimit proves the actual
original strict-prefix cocone is colimiting, with every original leg. -/
def prefixIsColimitOfLatchingMapIso (F : O ⥤ C) (j : O)
    [hIso : IsIso (ReedyStructure.latchingMap (ordinalReedy O) F j)] :
    IsColimit ((Set.principalSegIio j).cocone F) := by
  let ePoint := @asIso C _ _ _ (ReedyStructure.latchingMap (ordinalReedy O) F j) hIso
  let e : colimit.cocone ((ordinalReedy O).latchingDiagram F j) ≅
      (ordinalReedy O).latchingCocone F j :=
    Cocone.ext ePoint (fun a => (ordinalReedy O).latchingMap_ι F j a)
  have h : IsColimit ((ordinalReedy O).latchingCocone F j) :=
    IsColimit.ofIsoColimit (colimit.isColimit _) e
  exact (Functor.Final.isColimitWhiskerEquiv (latchingToPrefix j)
    ((Set.principalSegIio j).cocone F)) h

end PrefixColimits

section CompactLimits

attribute [local instance] IsFiltered.isConnected

variable [OrderBot O] [SuccOrder O]
  {C : Type u} [Category.{v} C] [ModelCategory C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]
  [∀ k, HasLimitsOfShape ((ordinalReedy O).Matching k) C]

omit [SuccOrder O] in
/-- Compactness of the actual generating domains and codomains proves
I-injectivity at the original target's actual limit cocone, in both columns. -/
theorem smoothingFactor_limit_latching_trivialFibration
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f))
    (j : O) (hj : Order.IsSuccLimit j) :
    trivialFibrations C (ReedyStructure.StageFactory.latchingP (ordinalReedy O)
      (rootedArrow F).hom (smoothingLowerFactor F j) j rfl) := by
  let r := ordinalReedy O
  let L := smoothingLowerFactor F j
  have hd : r.degree j = j := rfl
  let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  let _ : IsFiltered (r.Latching j) := IsFiltered.of_equivalence (latchingPrefixEquivalence j).symm
  let p := Functor.whiskerLeft (r.latchingBelow j hd) L.p
  have hTarget : IsColimit (r.latchingCocone F j) :=
    latchingIsColimitOfPrefix F j (F.isColimitOfIsWellOrderContinuous j hj)
  have hSourceMaps : ∀ (a b : r.Latching j) (f : a ⟶ b),
      P ((r.lowerLatchingDiagram L.Z j hd).map f) := by
    intro a b f
    change P ((smoothingFactor F).Z.map (r.latchingComparison f))
    exact hCof _ (smoothingFactor_map_cofibration F (leOfHom (r.latchingComparison f)))
  have hTargetMaps : ∀ (a b : r.Latching j) (f : a ⟶ b),
      P ((r.latchingDiagram F j).map f) := by
    intro a b f
    exact hF _ _ (r.latchingComparison f)
  have hp : ∀ a : r.Latching j, I.rlp (p.app a) := by
    intro a
    change I.rlp ((smoothingFactor F).p.app (r.latchingSource a))
    rw [hI]
    exact smoothingFactor_comparison_trivialFibration F (r.latchingSource a)
  have hq : ∀ a : r.Latching j,
      (colimit.cocone (r.lowerLatchingDiagram L.Z j hd)).ι.app a ≫
        ReedyStructure.StageFactory.latchingP r (rootedArrow F).hom L j hd =
          p.app a ≫ (r.latchingCocone F j).ι.app a := by
    intro a
    change colimit.ι (r.lowerLatchingDiagram L.Z j hd) a ≫
        (colimMap p ≫ ReedyStructure.latchingMap r F j) =
      p.app a ≫ F.map (r.latchingArrow a)
    calc
      _ = (colimit.ι (r.lowerLatchingDiagram L.Z j hd) a ≫ colimMap p) ≫
          ReedyStructure.latchingMap r F j := (Category.assoc _ _ _).symm
      _ = (p.app a ≫ colimit.ι (r.latchingDiagram F j) a) ≫
          ReedyStructure.latchingMap r F j :=
        congrArg (fun k => k ≫ ReedyStructure.latchingMap r F j) (ι_colimMap p a)
      _ = p.app a ≫ F.map (r.latchingArrow a) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => p.app a ≫ k) (r.latchingMap_ι F j a))
  have h := rlp_of_filtered_colimit_of_compact hCompact p
    (colimit.cocone (r.lowerLatchingDiagram L.Z j hd)) (r.latchingCocone F j)
    (colimit.isColimit _) hTarget
    (ReedyStructure.StageFactory.latchingP r (rootedArrow F).hom L j hd)
    hq hp hSourceMaps hTargetMaps
  rwa [hI] at h

omit [SuccOrder O] in
/-- The stationary source factory makes the produced diagram continuous
at every original limit. Its canonical cocone has the original prefix legs. -/
theorem smoothingFactor_isWellOrderContinuous
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f)) :
    (smoothingFactor F).Z.IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have hL := smoothingFactor_limit_latching_trivialFibration I P hI hCompact hCof F hF j hj
    have hC := coefficientMap_trivialFibration_of_latching F j hj.not_isMin hL
    let _ : IsIso (ReedyStructure.latchingMap (ordinalReedy O) (smoothingFactor F).Z j) :=
      smoothingFactor_latchingMap_isIso_of_coefficient F j hj.not_isMin hC
    exact prefixIsColimitOfLatchingMapIso (smoothingFactor F).Z j⟩

end CompactLimits

section WeakComposite

variable [OrderBot O] [SuccOrder O]
  {C : Type u} [Category.{v} C] [ModelCategory C]
  [∀ k, HasColimitsOfShape ((ordinalReedy O).Latching k) C]
  [∀ k, HasLimitsOfShape ((ordinalReedy O).Matching k) C]

omit [SuccOrder O] in
/-- A weak original transition makes the actual smoothing transition a
trivial cofibration, by its two genuine coefficient comparisons. -/
theorem smoothingFactor_map_trivialCofibration (F : O ⥤ C)
    {i j : O} (hij : i ≤ j) (hF : weakEquivalences C (F.map (homOfLE hij))) :
    trivialCofibrations C ((smoothingFactor F).Z.map (homOfLE hij)) := by
  let q := smoothingFactor F
  refine ⟨smoothingFactor_map_cofibration F hij, ?_⟩
  have hleft : weakEquivalences C (q.p.app i ≫ F.map (homOfLE hij)) :=
    (weakEquivalences C).comp_mem _ _ (smoothingFactor_comparison_trivialFibration F i).2 hF
  have he := q.p.naturality (homOfLE hij)
  have hright : weakEquivalences C (q.Z.map (homOfLE hij) ≫ q.p.app j) := he.symm ▸ hleft
  exact (weakEquivalences C).of_postcomp _ _
    (smoothingFactor_comparison_trivialFibration F j).2 hright

variable [HasColimitsOfShape O C]

/-- Strong relative compactness closes the original continuous weak chain
at its actual supplied endpoint cocone. Both columns and every endpoint leg
are retained; no weak-colimit or target-factorization conclusion is assumed. -/
theorem weak_at_original_cocone_of_compact
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I P) (hCof : cofibrations C ≤ P)
    (F : O ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (i j : O) (f : i ⟶ j), P (F.map f))
    (hWeak : ∀ j : O, ¬ IsMax j → weakEquivalences C (F.map (homOfLE (Order.le_succ j))))
    (cF : Cocone F) (hCF : IsColimit cF) : weakEquivalences C (cF.ι.app ⊥) := by
  let q := smoothingFactor F
  let Q := q.Z
  let _ : Q.IsWellOrderContinuous := smoothingFactor_isWellOrderContinuous I P hI hCompact hCof F hF
  let p : colimit Q ⟶ cF.pt :=
    (colimit.isColimit Q).desc (Cocone.mk cF.pt (q.p ≫ cF.ι))
  have hp (j : O) : colimit.ι Q j ≫ p = q.p.app j ≫ cF.ι.app j :=
    (colimit.isColimit Q).fac (Cocone.mk cF.pt (q.p ≫ cF.ι)) j
  have hQ : ∀ (i j : O) (f : i ⟶ j), P (Q.map f) := by
    intro i j f
    exact hCof _ (smoothingFactor_map_cofibration F (leOfHom f))
  have hComparison : ∀ j : O, I.rlp (q.p.app j) := by
    intro j
    rw [hI]
    exact smoothingFactor_comparison_trivialFibration F j
  have hpI : I.rlp p := rlp_of_filtered_colimit_of_compact hCompact q.p
    (colimit.cocone Q) cF (colimit.isColimit Q) hCF p hp hComparison hQ hF
  have hpT : trivialFibrations C p := hI ▸ hpI
  let _ : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape O := by
    rw [← fibrations_llp C]
    infer_instance
  let t : (trivialCofibrations C).TransfiniteCompositionOfShape O (colimit.ι Q ⊥) :=
    { F := Q
      isoBot := Iso.refl _
      incl := (colimit.cocone Q).ι
      isColimit := colimit.isColimit Q
      fac := Category.id_comp _
      map_mem j hj := smoothingFactor_map_trivialCofibration F (Order.le_succ j) (hWeak j hj) }
  have ht : trivialCofibrations C (colimit.ι Q ⊥) :=
    (trivialCofibrations C).transfiniteCompositionsOfShape_le O _ t.mem
  let i₀ : F.obj ⊥ ⟶ Q.obj ⊥ := q.i.app ⊥
  let p₀ : Q.obj ⊥ ⟶ F.obj ⊥ := q.p.app ⊥
  have hroot : i₀ ≫ p₀ = 𝟙 (F.obj ⊥) :=
    (congr_app q.fac ⊥).trans (rootedArrow_hom_bot F)
  have hrootWeak : weakEquivalences C i₀ :=
    (weakEquivalences C).of_postcomp _ _ (smoothingFactor_comparison_trivialFibration F ⊥).2
      (hroot.symm ▸ (weakEquivalences C).id_mem _)
  have hp₀ : colimit.ι Q ⊥ ≫ p = p₀ ≫ cF.ι.app ⊥ := hp ⊥
  have he : (i₀ ≫ colimit.ι Q ⊥) ≫ p = cF.ι.app ⊥ := by
    calc
      _ = i₀ ≫ (colimit.ι Q ⊥ ≫ p) := Category.assoc _ _ _
      _ = i₀ ≫ (p₀ ≫ cF.ι.app ⊥) := congrArg (fun k => i₀ ≫ k) hp₀
      _ = (i₀ ≫ p₀) ≫ cF.ι.app ⊥ := (Category.assoc _ _ _).symm
      _ = (𝟙 (F.obj ⊥)) ≫ cF.ι.app ⊥ := congrArg (fun k => k ≫ cF.ι.app ⊥) hroot
      _ = cF.ι.app ⊥ := Category.id_comp _
  exact he ▸ (weakEquivalences C).comp_mem _ _
    ((weakEquivalences C).comp_mem _ _ hrootWeak ht.2) hpT.2

end WeakComposite

end CategoryTheory.OrdinalCofibrationSmoothing

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  [P.IsStableUnderTransfiniteComposition.{w}]
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}

/-- Every comparison between actual original stages lies in the same
transfinite-stable class, using its original tail and prefix cocones. -/
theorem TransfiniteCompositionOfShape.map_mem_of_stable
    (c : P.TransfiniteCompositionOfShape O f) {i j : O} (g : i ⟶ j) : P (c.F.map g) := by
  let t := (c.ici i).iic (⟨j, leOfHom g⟩ : Set.Ici i)
  have h := P.transfiniteCompositionsOfShape_le (Set.Iic (⟨j, leOfHom g⟩ : Set.Ici i)) _ t.mem
  change P (c.F.map (homOfLE (leOfHom g))) at h
  exact h

end CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The compact-source argument recovers the unchanged whole original
transfinite arrow through its original bottom isomorphism and endpoint cocone. -/
theorem weak_of_transfiniteComposition_of_compact
    (I P : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I P) (hCof : cofibrations C ≤ P)
    [P.IsStableUnderTransfiniteComposition.{w}]
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    [HasColimitsOfShape O C]
    [∀ j, HasColimitsOfShape ((OrdinalCofibrationSmoothing.ordinalReedy O).Latching j) C]
    [∀ j, HasLimitsOfShape ((OrdinalCofibrationSmoothing.ordinalReedy O).Matching j) C]
    {X Y : C} {f : X ⟶ Y}
    (c : (P ⊓ weakEquivalences C).TransfiniteCompositionOfShape O f) :
    weakEquivalences C f := by
  let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  let cp := c.ofLE inf_le_left
  have h : weakEquivalences C (c.incl.app ⊥) :=
    OrdinalCofibrationSmoothing.weak_at_original_cocone_of_compact I P hI hCompact hCof c.F
      (fun _ _ g => cp.map_mem_of_stable g)
      (fun j hj => (c.map_mem j hj).2) (Cocone.mk Y c.incl) c.isColimit
  have hroot : weakEquivalences C c.isoBot.inv := mem_weakEquivalences _
  exact c.fac ▸ (weakEquivalences C).comp_mem _ _ hroot h

section CompactCellularClosure

variable [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

/-- Within the actual compact-source transition class, couniversal weak
equivalences are closed under continuous transfinite composition. -/
theorem couniversalIntersection_isStableUnderTransfiniteComposition_of_compact
    (I S : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I S) (hCof : cofibrations C ≤ S)
    [S.IsStableUnderTransfiniteComposition.{w}] [S.IsStableUnderCobaseChange] :
    (couniversalWeakEquivalences C ⊓ S).IsStableUnderTransfiniteComposition.{w} where
  isStableUnderTransfiniteCompositionOfShape O _ _ _ _ :=
    { le := by
        intro X Y f hf
        obtain ⟨c⟩ := hf
        refine ⟨?_, ?_⟩
        · intro A B a q b sq
          let d := c.cobaseChange a sq
          have hPush : (couniversalWeakEquivalences C ⊓ S).pushouts ≤
              S ⊓ weakEquivalences C := by
            intro U V g hg
            obtain ⟨P, Q, i, u, v, hi, si⟩ := hg
            exact ⟨MorphismProperty.of_isPushout si hi.2, hi.1 U V u g v si⟩
          exact weak_of_transfiniteComposition_of_compact I S hI hCompact hCof (d.ofLE hPush)
        · exact S.transfiniteCompositionsOfShape_le O _ (c.ofLE inf_le_right).mem }

/-- The original full cellular closure is couniversally weak, including
the actual arbitrary coproduct cofans, pushouts and original endpoint maps. -/
theorem cellularClosure_le_couniversal_of_compact
    (I S Q : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I S) (hCof : cofibrations C ≤ S)
    [S.IsStableUnderTransfiniteComposition.{w}] [S.IsStableUnderCobaseChange]
    (hQ : Q ≤ couniversalWeakEquivalences C) (hQS : Q ≤ S) :
    SmallObject.CellularNormalization.cellularClosure.{w, w} Q ≤ couniversalWeakEquivalences C := by
  let T := couniversalWeakEquivalences C ⊓ S
  let _ : T.IsStableUnderTransfiniteComposition.{w} :=
    couniversalIntersection_isStableUnderTransfiniteComposition_of_compact I S hI hCompact hCof
  let _ : T.IsStableUnderCobaseChange := inferInstance
  let _ : T.IsStableUnderCoproducts.{w} := isStableUnderCoproducts_of_cobase_transfinite T
  have hQT : Q ≤ T := le_inf hQ hQS
  have hPush : (coproducts.{w} Q).pushouts ≤ T :=
    (pushouts_le_iff (P := coproducts.{w} Q)).2
      ((coproducts_le_iff (P := Q)).2 hQT)
  exact ((transfiniteCompositions_monotone hPush).trans
    (transfiniteCompositions_le T)).trans inf_le_left

end CompactCellularClosure

section IndependentCellularUniverses

variable [HasColimitsOfSize.{w, w} C] [UnivLE.{w', w}] [UnivLE.{ν, w}]

/-- The weak-transfinite alternative closes the actual cellular class,
with independent original stage and coproduct-label universes. -/
theorem cellularClosure_le_couniversal_of_weak_transfinite
    (Q : MorphismProperty C)
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]
    (hQ : Q ≤ couniversalWeakEquivalences C) :
    SmallObject.CellularNormalization.cellularClosure.{w', ν} Q ≤
      couniversalWeakEquivalences C := by
  let T := couniversalWeakEquivalences C
  have hTmax : T.IsStableUnderTransfiniteComposition.{w} :=
    couniversalWeakEquivalences_isStableUnderTransfiniteComposition
  have hTν : T.IsStableUnderTransfiniteComposition.{ν} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  let _ : T.IsStableUnderTransfiniteComposition.{w'} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  have hCop : HasCoproducts.{ν} C :=
    fun _ => HasColimitsOfShape.of_essentiallySmall C _
  let _ : T.IsStableUnderCoproducts.{ν} :=
    @isStableUnderCoproducts_of_cobase_transfinite _ _ T inferInstance hTν hCop
  have hPush : (coproducts.{ν} Q).pushouts ≤ T :=
    (pushouts_le_iff (P := coproducts.{ν} Q)).2 ((coproducts_le_iff (P := Q)).2 hQ)
  exact (transfiniteCompositions_monotone hPush).trans (transfiniteCompositions_le T)

variable [HasLimitsOfSize.{w, w} C]

/-- Strong compact generating sources close the same actual cellular class,
retaining independent original ordinal and actual coproduct-label universes. -/
theorem cellularClosure_le_couniversal_of_compact_independent
    (I S Q : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hCompact : CompactGeneratingSources.{w} I S) (hCof : cofibrations C ≤ S)
    [S.IsStableUnderTransfiniteComposition.{w}] [S.IsStableUnderCobaseChange]
    (hQ : Q ≤ couniversalWeakEquivalences C) (hQS : Q ≤ S) :
    SmallObject.CellularNormalization.cellularClosure.{w', ν} Q ≤
      couniversalWeakEquivalences C := by
  let T := couniversalWeakEquivalences C ⊓ S
  have hTmax : T.IsStableUnderTransfiniteComposition.{w} :=
    couniversalIntersection_isStableUnderTransfiniteComposition_of_compact I S hI hCompact hCof
  have hTν : T.IsStableUnderTransfiniteComposition.{ν} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  let _ : T.IsStableUnderTransfiniteComposition.{w'} :=
    @IsStableUnderTransfiniteComposition.shrink _ _ T hTmax inferInstance
  let _ : T.IsStableUnderCobaseChange := inferInstance
  have hCop : HasCoproducts.{ν} C :=
    fun _ => HasColimitsOfShape.of_essentiallySmall C _
  let _ : T.IsStableUnderCoproducts.{ν} :=
    @isStableUnderCoproducts_of_cobase_transfinite _ _ T inferInstance hTν hCop
  have hQT : Q ≤ T := le_inf hQ hQS
  have hPush : (coproducts.{ν} Q).pushouts ≤ T :=
    (pushouts_le_iff (P := coproducts.{ν} Q)).2 ((coproducts_le_iff (P := Q)).2 hQT)
  exact ((transfiniteCompositions_monotone hPush).trans
    (transfiniteCompositions_le T)).trans inf_le_left

end IndependentCellularUniverses

end HomotopicalAlgebra

namespace HomotopicalAlgebra.OperadicAcyclicCells

open CategoryTheory.OperadicOrbitCells
open CategoryTheory.SmallObject.CellularNormalization

variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C]

/-- The actual positive heterogeneous orbit cells of all original cofibrations,
including arbitrary equivariant coefficients and actual coproduct labels. -/
def cofibrationCells : MorphismProperty C :=
  cellularClosure.{w, ν} (orbitGenerators (cofibrations C))

/-- The acyclic part of conventional symmetric h-monoidality tests every
literal positive-family orbit arrow and every original equivariant coefficient. -/
structure AcyclicSymmetricHMonoidality : Prop where
  couniversal (s : PositiveOrbitFamily C) (hs : ∀ r, trivialCofibrations C (s.arrows r).hom) :
    couniversalWeakEquivalences C (familyOrbitArrow s).hom

/-- The ordinary weak-plus-h-cofibration source formulation, equivalent to
the couniversal formulation in the original left proper model. -/
structure AcyclicSymmetricHMonoidalityOrdinary : Prop where
  acyclic (s : PositiveOrbitFamily C) (hs : ∀ r, trivialCofibrations C (s.arrows r).hom) :
    acyclicHCofibrations C (familyOrbitArrow s).hom

/-- Strong admissible generation concerns both endpoints of the chosen
generating I arrows, compact relative to the actual full coefficient-orbit cells. -/
def StrongAdmissibleGeneration (I : MorphismProperty C) : Prop :=
  CompactGeneratingSources.{w} I (cofibrationCells.{w, ν} C)

variable {C}

/-- The original full cofibration orbit-cell class is structurally closed;
the empty witnesses are actual empty coproduct cofans, not empty PP unit arrows. -/
theorem cofibrationCells_stable :
    (cofibrationCells.{w, ν} C).IsStableUnderCobaseChange ∧
      (cofibrationCells.{w, ν} C).IsStableUnderCoproducts.{w} ∧
      (cofibrationCells.{w, ν} C).IsStableUnderTransfiniteComposition.{w} := by
  let D : PEmpty.{ν + 1} → C := fun i => i.elim
  let _ : HasColimitsOfShape (Discrete PEmpty.{ν + 1}) C :=
    HasColimitsOfShape.of_essentiallySmall C _
  exact cellularClosure_stable (orbitGenerators (cofibrations C))
    (colimit.cocone (Discrete.functor D)) (colimit.cocone (Discrete.functor D))
    (colimit.isColimit _) (colimit.isColimit _)

/-- The original unary/unit Arrow comparison places every source cofibration
in this exact orbit-cell class, with no cofibrancy condition on the unit. -/
theorem cofibrations_le_cofibrationCells : cofibrations C ≤ cofibrationCells.{w, ν} C := by
  let _ : (cofibrationCells.{w, ν} C).IsStableUnderCobaseChange := cofibrationCells_stable.1
  have hOrbit : orbitGenerators (cofibrations C) ≤ cofibrationCells.{w, ν} C :=
    (le_coproducts _).trans ((le_pushouts _).trans (le_transfiniteCompositions _))
  exact (le_orbitGenerators_isoClosure (cofibrations C)).trans
    ((isoClosure_le_iff _ _).2 hOrbit)

/-- Trivial-cofibration orbit generators remain in the same full source cell class. -/
theorem trivialOrbitGenerators_le_cofibrationCells :
    orbitGenerators (trivialCofibrations C) ≤ cofibrationCells.{w, ν} C := by
  have h := orbitGenerators_monotone (C := C)
    (show trivialCofibrations C ≤ cofibrations C from inf_le_left)
  exact h.trans ((le_coproducts _).trans ((le_pushouts _).trans (le_transfiniteCompositions _)))

/-- The source couniversal criterion is exactly a condition on every
positive finite family, rather than a certificate about its cellular closure. -/
theorem AcyclicSymmetricHMonoidality.generators_le (h : AcyclicSymmetricHMonoidality C) :
    orbitGenerators (trivialCofibrations C) ≤ couniversalWeakEquivalences C :=
  (orbitGenerators_le_iff _ _).2 h.couniversal

/-- Original left properness converts the ordinary acyclic h-cofibration
source condition into the direct couniversal source condition. -/
theorem AcyclicSymmetricHMonoidalityOrdinary.toCouniversal [IsLeftProper C]
    (h : AcyclicSymmetricHMonoidalityOrdinary C) : AcyclicSymmetricHMonoidality C where
  couniversal s hs := acyclicHCofibrations_le_couniversalWeakEquivalences _ (h.acyclic s hs)

variable [UnivLE.{w', w}] [UnivLE.{ν, w}]

/-- The first original A6 alternative: actual positive orbit attachments
and their entire cellular closure are couniversally weak under weak-transfinite closure. -/
theorem operadic_acyclic_cells_of_weak_transfinite
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]
    (h : AcyclicSymmetricHMonoidality C) :
    cellularClosure.{w', ν} (orbitGenerators (trivialCofibrations C)) ≤
      couniversalWeakEquivalences C :=
  cellularClosure_le_couniversal_of_weak_transfinite.{w, w', ν} _ h.generators_le

/-- The second original A6 alternative: original left properness and
strong admissible generation close the same full actual positive orbit-cell class. -/
theorem operadic_acyclic_cells_of_strong_admissible
    [HasLimitsOfSize.{w, w} C] [IsLeftProper C]
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hStrong : StrongAdmissibleGeneration.{w, ν} C I)
    (h : AcyclicSymmetricHMonoidalityOrdinary C) :
    cellularClosure.{w', ν} (orbitGenerators (trivialCofibrations C)) ≤
      couniversalWeakEquivalences C := by
  let S := cofibrationCells.{w, ν} C
  let _ : S.IsStableUnderCobaseChange := cofibrationCells_stable.1
  let _ : S.IsStableUnderTransfiniteComposition.{w} := cofibrationCells_stable.2.2
  exact cellularClosure_le_couniversal_of_compact_independent.{w, w', ν} I S _ hI hStrong
    cofibrations_le_cofibrationCells h.toCouniversal.generators_le
    trivialOrbitGenerators_le_cofibrationCells

end HomotopicalAlgebra.OperadicAcyclicCells

namespace HomotopicalAlgebra.OperadicAcyclicCells

section OriginalProfiles

universe uc

open CategoryTheory.Operad CategoryTheory.OperadicOrbitCells
open CategoryTheory.OperadicOrbitCells.ProfileGeometry
open CategoryTheory.SmallObject.CellularNormalization

variable {W : Type uc} {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C]

/-- The original symmetric tensor structure supplies every actual profile tensor. -/
local instance originalProfileFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- The actual global orbit-cell closure retains all cobase changes and full cofans. -/
theorem orbitCellularClosure_stable (Q : MorphismProperty C) :
    (cellularClosure.{w, ν} (orbitGenerators Q)).IsStableUnderCobaseChange ∧
      (cellularClosure.{w, ν} (orbitGenerators Q)).IsStableUnderCoproducts.{w} ∧
      (cellularClosure.{w, ν} (orbitGenerators Q)).IsStableUnderTransfiniteComposition.{w} := by
  let D : PEmpty.{ν + 1} → C := fun i => i.elim
  let _ : HasColimitsOfShape (Discrete PEmpty.{ν + 1}) C :=
    HasColimitsOfShape.of_essentiallySmall C _
  exact cellularClosure_stable (orbitGenerators Q)
    (colimit.cocone (Discrete.functor D)) (colimit.cocone (Discrete.functor D))
    (colimit.isColimit _) (colimit.isColimit _)

/-- The full original positive profile boundary orbit is an actual orbit cell,
with arbitrary original Aut coefficient and no smallness condition on the palette. -/
theorem profileOrbitArrow_cellular (Q : MorphismProperty C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, Q (x (P.inputColor i))) :
    cellularClosure.{w, ν} (orbitGenerators Q) (profileOrbitArrow x P Y).hom := by
  let T := cellularClosure.{w, ν} (orbitGenerators Q)
  let _ : T.IsStableUnderCobaseChange := (orbitCellularClosure_stable Q).1
  have hQ : orbitGenerators Q ≤ T :=
    (le_coproducts _).trans ((le_pushouts _).trans (le_transfiniteCompositions _))
  exact ((isoClosure_le_iff _ _).2 hQ) _
    (profileOrbitArrow_mem_isoClosure Q x P hP Y hx)

/-- The original ordered pushout-product orbit has the same full cellular membership. -/
theorem profileIteratedOrbitArrow_cellular (Q : MorphismProperty C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, Q (x (P.inputColor i))) :
    cellularClosure.{w, ν} (orbitGenerators Q) (profileIteratedOrbitArrow x P Y).hom := by
  let T := cellularClosure.{w, ν} (orbitGenerators Q)
  let _ : T.IsStableUnderCobaseChange := (orbitCellularClosure_stable Q).1
  exact (T.arrow_iso_iff (profileOrbitPushoutProductIso x P Y)).1
    (profileOrbitArrow_cellular Q x P hP Y hx)

variable [UnivLE.{ν, w}]

/-- The first source alternative closes the actual original positive profile orbit,
including every actual cobase-change map, without left properness. -/
theorem profileOrbitArrow_couniversal_of_weak_transfinite
    [(weakEquivalences C).IsStableUnderTransfiniteComposition.{w}]
    (h : AcyclicSymmetricHMonoidality C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, trivialCofibrations C (x (P.inputColor i))) :
    couniversalWeakEquivalences C (profileOrbitArrow x P Y).hom :=
  operadic_acyclic_cells_of_weak_transfinite.{w, w, ν} h _
    (profileOrbitArrow_cellular (trivialCofibrations C) x P hP Y hx)

/-- The second source alternative closes the same original arbitrary-coefficient profile
using only the original left properness and compact generating I endpoints. -/
theorem profileOrbitArrow_couniversal_of_strong_admissible
    [HasLimitsOfSize.{w, w} C] [IsLeftProper C]
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
    (hStrong : StrongAdmissibleGeneration.{w, ν} C I)
    (h : AcyclicSymmetricHMonoidalityOrdinary C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, trivialCofibrations C (x (P.inputColor i))) :
    couniversalWeakEquivalences C (profileOrbitArrow x P Y).hom :=
  operadic_acyclic_cells_of_strong_admissible.{w, w, ν} I hI hStrong h _
    (profileOrbitArrow_cellular (trivialCofibrations C) x P hP Y hx)

end OriginalProfiles

end HomotopicalAlgebra.OperadicAcyclicCells
