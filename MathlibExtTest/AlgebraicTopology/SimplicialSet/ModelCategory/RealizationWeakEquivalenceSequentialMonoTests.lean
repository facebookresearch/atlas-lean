/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

/-!
# Sequential-mono realization weak-equivalence tests

The clients pin the identity transformation and the intended application to
chains of subcomplex inclusions.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty

universe u

namespace MathlibExtTest.RealizationWeakEquivalenceSequentialMono

example :
    (SSet.KanComplex.W : MorphismProperty SSet.{u}).IsStableUnderColimitsOfShape ℕ :=
  inferInstance

example :
    (SSet.KanComplex.W : MorphismProperty SSet.{1}).IsStableUnderColimitsOfShape ℕ :=
  inferInstance

example :
    (SSet.KanComplex.W : MorphismProperty SSet.{0}).IsStableUnderColimitsOfShape ℕ :=
  inferInstance

example : True := by
  fail_if_success
    have : MorphismProperty.IsStableUnderFilteredColimits.{1, 1}
        (SSet.KanComplex.W : MorphismProperty SSet.{0}) := inferInstance
  trivial

example : True := by
  fail_if_success
    have : (SSet.KanComplex.W : MorphismProperty SSet.{u}).IsStableUnderColimitsOfShape
        (Discrete PEmpty) := inferInstance
  trivial

example {F : ℕ ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (F.map f)) :
    SSet.realizationWeakEquivalences (𝟙 c.pt) := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    (alpha := 𝟙 F) hc hc (𝟙 c.pt)
  · intro n
    simp
  · exact hF
  · exact hF
  · intro n
    exact SSet.realizationWeakEquivalences.id_mem (F.obj n)

abbrev subcomplexChain {X : SSet.{u}} (A : ℕ → X.Subcomplex)
    (hA : Monotone A) : ℕ ⥤ SSet.{u} :=
  hA.functor ⋙ SSet.Subcomplex.toSSetFunctor

example {X Y : SSet.{u}}
    (A : ℕ → X.Subcomplex) (hA : Monotone A)
    (B : ℕ → Y.Subcomplex) (hB : Monotone B)
    (alpha : subcomplexChain A hA ⟶ subcomplexChain B hB)
    {cA : Cocone (subcomplexChain A hA)}
    {cB : Cocone (subcomplexChain B hB)}
    (hcA : IsColimit cA) (hcB : IsColimit cB)
    (phi : cA.pt ⟶ cB.pt)
    (hphi : ∀ n, cA.ι.app n ≫ phi = alpha.app n ≫ cB.ι.app n)
    (hAlpha : ∀ n, SSet.realizationWeakEquivalences (alpha.app n)) :
    SSet.realizationWeakEquivalences phi := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    alpha hcA hcB phi hphi
  · intro i j f
    change Mono (SSet.Subcomplex.homOfLE (hA (leOfHom f)))
    infer_instance
  · intro i j f
    change Mono (SSet.Subcomplex.homOfLE (hB (leOfHom f)))
    infer_instance
  · exact hAlpha

abbrev emptyChain (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  subcomplexChain (fun _ : ℕ ↦ (⊥ : X.Subcomplex)) (fun _ _ _ ↦ le_rfl)

example {X : SSet.{u}} {c : Cocone (emptyChain X)} (hc : IsColimit c) :
    SSet.realizationWeakEquivalences (𝟙 c.pt) := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    (alpha := 𝟙 (emptyChain X)) hc hc (𝟙 c.pt)
  · intro n
    simp
  · intro i j f
    change Mono (SSet.Subcomplex.homOfLE (le_rfl : (⊥ : X.Subcomplex) ≤ ⊥))
    infer_instance
  · intro i j f
    change Mono (SSet.Subcomplex.homOfLE (le_rfl : (⊥ : X.Subcomplex) ≤ ⊥))
    infer_instance
  · intro n
    exact SSet.realizationWeakEquivalences.id_mem _

example {X : SSet.{u}} (A : ℕ → X.Subcomplex) (hA : Monotone A) (n : ℕ) :
    Mono ((subcomplexChain A hA).map (homOfLE (Nat.le_succ n))) := by
  change Mono (SSet.Subcomplex.homOfLE (hA (Nat.le_succ n)))
  infer_instance

section TransfiniteMono

universe v

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y : SSet.{u}} {f : X ⟶ Y}

example
    (hf : (SSet.realizationWeakEquivalences.{u} ⊓
      MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape J f)
    [(SSet.KanComplex.W : MorphismProperty SSet.{u}).IsStableUnderTransfiniteCompositionOfShape J] :
    SSet.realizationWeakEquivalences f :=
  SSet.realizationWeakEquivalences.of_transfiniteComposition_mono hf

section WitnessStages

variable (hf : (SSet.realizationWeakEquivalences.{u} ⊓
  MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape J f)

example : hf.F.obj ⊥ ≅ X := hf.isoBot

example (j : J) (hj : ¬ IsMax j) :
    (SSet.realizationWeakEquivalences.{u} ⊓
      MorphismProperty.monomorphisms SSet.{u})
      (hf.F.map (homOfLE (Order.le_succ j))) :=
  hf.map_mem j hj

example (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone hf.F) :=
  hf.F.isColimitOfIsWellOrderContinuous m hm

end WitnessStages

section SameUniverse

variable {K : Type u} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K] [NoMaxOrder K]

example : MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
    (SSet.KanComplex.W : MorphismProperty SSet.{u}) K :=
  inferInstance

example {A B : SSet.{u}} {g : A ⟶ B}
    (hg : (SSet.realizationWeakEquivalences.{u} ⊓
      MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape K g) :
    SSet.realizationWeakEquivalences g :=
  SSet.realizationWeakEquivalences.of_transfiniteComposition_mono hg

end SameUniverse

section UniverseOne

variable {K : Type 1} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K] [NoMaxOrder K]

example {A B : SSet.{1}} {g : A ⟶ B}
    (hg : (SSet.realizationWeakEquivalences.{1} ⊓
      MorphismProperty.monomorphisms SSet.{1}).TransfiniteCompositionOfShape K g) :
    SSet.realizationWeakEquivalences g :=
  SSet.realizationWeakEquivalences.of_transfiniteComposition_mono hg

end UniverseOne

section UniverseZero

variable {K : Type} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K] [NoMaxOrder K]

example {A B : SSet.{0}} {g : A ⟶ B}
    (hg : (SSet.realizationWeakEquivalences.{0} ⊓
      MorphismProperty.monomorphisms SSet.{0}).TransfiniteCompositionOfShape K g) :
    SSet.realizationWeakEquivalences g :=
  SSet.realizationWeakEquivalences.of_transfiniteComposition_mono hg

end UniverseZero

section MissingStageProperty

variable [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
  (SSet.KanComplex.W : MorphismProperty SSet.{u}) J]

example (_hf : SSet.realizationWeakEquivalences.{u}.TransfiniteCompositionOfShape J f) : True := by
  fail_if_success
    have _ := SSet.realizationWeakEquivalences.of_transfiniteComposition_mono _hf
  trivial

example (_hf : (MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape J f) :
    True := by
  fail_if_success
    have _ := SSet.realizationWeakEquivalences.of_transfiniteComposition_mono _hf
  trivial

end MissingStageProperty

section MissingWStability

example (_hf : (SSet.realizationWeakEquivalences.{u} ⊓
    MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape J f) : True := by
  fail_if_success
    have _ := SSet.realizationWeakEquivalences.of_transfiniteComposition_mono _hf
  trivial

end MissingWStability

section NoUnrestrictedInstance

example : True := by
  fail_if_success
    let _ : MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
        SSet.realizationWeakEquivalences.{u} J :=
      inferInstance
  trivial

end NoUnrestrictedInstance

section MissingNoMax

variable {K : Type u} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K]

example : True := by
  fail_if_success
    let _ : MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
        (SSet.KanComplex.W : MorphismProperty SSet.{u}) K :=
      inferInstance
  trivial

end MissingNoMax

section OverlargeShape

variable {K : Type 1} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K] [NoMaxOrder K]

example : True := by
  fail_if_success
    let _ : MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
        (SSet.KanComplex.W : MorphismProperty SSet.{0}) K :=
      inferInstance
  trivial

end OverlargeShape

#print axioms SSet.realizationWeakEquivalences.of_transfiniteComposition_mono

end TransfiniteMono

end MathlibExtTest.RealizationWeakEquivalenceSequentialMono
