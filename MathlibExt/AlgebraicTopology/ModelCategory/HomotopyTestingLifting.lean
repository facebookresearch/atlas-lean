/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTestingRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingFibrations
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

/-!
# Monic testing equivalences and lifting into naive fibrant targets

Replace the target by an anodyne map into a naive fibrant object. A monic
testing equivalence then lifts against every naive fibration with naive
fibrant codomain. Conversely, two actual lifts make the replaced map an
arrow retract of an anodyne map, and two-out-of-three cancels the replacement.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Proposition 2.4.30 (printed pp.61–62 / PDF pp.77–78), with explicit
generic factorization hypotheses. The original source and target need not
be naive fibrant. The class formula retains the monomorphism intersection.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- An original monomorphism is a testing equivalence exactly when it lifts
against naive fibrations whose codomains are naive fibrant. -/
theorem testingEquivalences_iff_llp_naiveFibrantCodomain
    {A B : C} (i : A ⟶ B) [Mono i] :
    P.testingEquivalences An i ↔
      (An.naiveFibrations ⊓
        MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects).llp i := by
  let dB := MorphismProperty.factorizationData An An.rlp (terminal.from B)
  have hB' : An.naiveFibrantObjects dB.Z := by
    change An.rlp (terminal.from dB.Z)
    rw [show terminal.from dB.Z = dB.p from terminal.hom_ext _ _]
    exact dB.hp
  have : Mono dB.i := le_monomorphisms (P := P) (An := An) dB.i dB.hi
  have hjW : P.testingEquivalences An dB.i :=
    anodyne_le_testingEquivalences P An dB.i dB.hi
  constructor
  · intro hi X T p hp
    have hcompW : P.testingEquivalences An (i ≫ dB.i) :=
      (P.testingEquivalences An).comp_mem i dB.i hi hjW
    have hAnComp : An (i ≫ dB.i) :=
      (testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant
        P An (i ≫ dB.i) hB').mp hcompW
    have : HasLiftingProperty (i ≫ dB.i) p := hp.1 _ hAnComp
    refine ⟨?_⟩
    intro a b sq
    obtain ⟨b', hb'⟩ :=
      (An.naiveFibrantObjects_iff_extensions T).mp hp.2.2 dB.i dB.hi b
    have sq' : CommSq a (i ≫ dB.i) p b' :=
      ⟨by rw [Category.assoc, hb']; exact sq.w⟩
    exact CommSq.HasLift.mk'
      { l := dB.i ≫ sq'.lift
        fac_left := by rw [← Category.assoc, sq'.fac_left]
        fac_right := by rw [Category.assoc, sq'.fac_right, hb'] }
  · intro hi
    let d := MorphismProperty.factorizationData An An.rlp (i ≫ dB.i)
    have hpR : (An.naiveFibrations ⊓
        MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects) d.p :=
      ⟨d.hp, trivial, hB'⟩
    have : HasLiftingProperty i d.p := hi d.p hpR
    have : HasLiftingProperty dB.i d.p := d.hp dB.i dB.hi
    -- Native composition lifts first across i, then across dB.i; the latter
    -- square has lower map 𝟙 dB.Z and supplies the split codomain component.
    have : HasLiftingProperty (i ≫ dB.i) d.p := inferInstance
    have hleft : An.rlp.llp d.i := by
      simpa only [llp_rlp_eq P An] using d.hi
    have hAnComp : An (i ≫ dB.i) := by
      have hcompLeft : An.rlp.llp (i ≫ dB.i) :=
        MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) hleft
      simpa only [llp_rlp_eq P An] using hcompLeft
    exact (P.testingEquivalences An).of_postcomp i dB.i hjW
      (anodyne_le_testingEquivalences P An (i ≫ dB.i) hAnComp)

/-- The full class formula preserves the monomorphism restriction. -/
theorem testingTrivialCofibrations_eq_inf_llp_naiveFibrantCodomain :
    P.testingTrivialCofibrations An = MorphismProperty.monomorphisms C ⊓
      (An.naiveFibrations ⊓
        MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects).llp := by
  ext A B i
  rw [P.testingTrivialCofibrations_iff An i, MorphismProperty.inf_iff]
  constructor
  · rintro ⟨hmono, hw⟩
    have : Mono i := hmono
    exact ⟨hmono, (testingEquivalences_iff_llp_naiveFibrantCodomain P An i).mp hw⟩
  · rintro ⟨hmono, hl⟩
    have : Mono i := hmono
    exact ⟨hmono, (testingEquivalences_iff_llp_naiveFibrantCodomain P An i).mpr hl⟩

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
