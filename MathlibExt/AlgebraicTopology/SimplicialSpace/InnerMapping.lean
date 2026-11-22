/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerSM7
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Raw inner mapping fibrations and weak invariance
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalCategory
open scoped SimplicialSpace.Inner Simplicial MonoidalCategory

namespace SimplicialSpace.ReedyModel

private theorem innerHom_preservesTerminal (X : SimplicialSpace.{u}) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SimplicialSpace.innerHomFunctor.obj (op X)) := by
  let _ : (SimplicialSpace.innerHomFunctor.obj (op X)).IsRightAdjoint :=
    ⟨_, ⟨SimplicialSpace.innerTensorHomAdjunction₂.adj X⟩⟩
  infer_instance

private theorem flipInnerHom_preservesTerminal (Z : SimplicialSpace.{u}) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (SimplicialSpace.innerHomFunctor.flip.obj Z) := by
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ
      (SimplicialSpace.innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ (SimplicialSpace.innerTensor K)
    let _ : (SimplicialSpace.innerTensor K).IsLeftAdjoint :=
      (SimplicialSpace.innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact SimplicialSpace.innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj
    (Discrete PEmpty.{1}) Z

/-- Cofibrant-arrow precomposition into a fibrant object is an actual Kan fibration. -/
theorem inner_precomp_fibration {A B : SimplicialSpace.{u}} (i : A ⟶ B) (Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    cofibrations SimplicialSpace.{u} i → IsFibrant Z →
      fibrations SSet.{u} ((SimplicialSpace.innerHomFunctor.map i.op).app Z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hZ
  let _ : IsFibrant Z := hZ
  let _ := innerHom_preservesTerminal A
  let _ := innerHom_preservesTerminal B
  let q := Functor.PullbackObjObj.ofIsTerminal SimplicialSpace.innerHomFunctor
    i (terminal.from Z) terminalIsTerminal
  exact inner_pullbackHom_fibration i (terminal.from Z) q hi
    ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)

/-- The original raw precomposition is trivial for an original trivial cofibration. -/
theorem inner_precomp_trivialFibration {A B : SimplicialSpace.{u}} (i : A ⟶ B)
    (Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → IsFibrant Z →
      trivialFibrations SSet.{u} ((SimplicialSpace.innerHomFunctor.map i.op).app Z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi hZ
  let _ : IsFibrant Z := hZ
  let _ := innerHom_preservesTerminal A
  let _ := innerHom_preservesTerminal B
  let q := Functor.PullbackObjObj.ofIsTerminal SimplicialSpace.innerHomFunctor
    i (terminal.from Z) terminalIsTerminal
  exact inner_pullbackHom_trivialFibration_of_left i (terminal.from Z) q hi
    ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)

/-- Raw postcomposition preserves the genuine Reedy fibration out of a cofibrant source. -/
theorem inner_postcomp_fibration (X : SimplicialSpace.{u}) {U V : SimplicialSpace.{u}} (p : U ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsCofibrant X → fibrations SimplicialSpace.{u} p →
      fibrations SSet.{u} ((SimplicialSpace.innerHomFunctor.obj (op X)).map p) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hX hp
  let _ : IsCofibrant X := hX
  let _ := flipInnerHom_preservesTerminal U
  let _ := flipInnerHom_preservesTerminal V
  let q := Functor.PullbackObjObj.ofIsInitial SimplicialSpace.innerHomFunctor
    (initial.to X) p initialIsInitial
  exact inner_pullbackHom_fibration (initial.to X) p q
    ((HomotopicalAlgebra.cofibration_iff _).1 inferInstance) hp

/-- Raw postcomposition preserves the genuine trivial Reedy fibration. -/
theorem inner_postcomp_trivialFibration (X : SimplicialSpace.{u}) {U V : SimplicialSpace.{u}}
    (p : U ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsCofibrant X → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} ((SimplicialSpace.innerHomFunctor.obj (op X)).map p) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hX hp
  let _ : IsCofibrant X := hX
  let _ := flipInnerHom_preservesTerminal U
  let _ := flipInnerHom_preservesTerminal V
  let q := Functor.PullbackObjObj.ofIsInitial SimplicialSpace.innerHomFunctor
    (initial.to X) p initialIsInitial
  exact inner_pullbackHom_trivialFibration_of_right (initial.to X) p q
    ((HomotopicalAlgebra.cofibration_iff _).1 inferInstance) hp

/-- The actual inner mapping end is Kan at the stated cofibrant/fibrant endpoints. -/
theorem innerHom_kanComplex (X Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsCofibrant X → IsFibrant Z →
      SSet.KanComplex ((SimplicialSpace.innerHomFunctor.obj (op X)).obj Z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hX hZ
  let _ : IsFibrant Z := hZ
  let _ := innerHom_preservesTerminal X
  have hp := inner_postcomp_fibration X (terminal.from Z) hX
    ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  let _ : Fibration ((SimplicialSpace.innerHomFunctor.obj (op X)).map (terminal.from Z)) :=
    (HomotopicalAlgebra.fibration_iff _).2 hp
  have hT :
      IsTerminal ((SimplicialSpace.innerHomFunctor.obj (op X)).obj (⊤_ SimplicialSpace.{u})) :=
    terminalIsTerminal.isTerminalObj (SimplicialSpace.innerHomFunctor.obj (op X)) _
  exact (HomotopicalAlgebra.isFibrant_iff_of_isTerminal
    ((SimplicialSpace.innerHomFunctor.obj (op X)).map (terminal.from Z)) hT).2 inferInstance

/-- Original weak arrows between cofibrant sources act weakly by raw precomposition. -/
theorem inner_precomp_weak_of_weak {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsCofibrant X → IsCofibrant Y → weakEquivalences SimplicialSpace.{u} f → IsFibrant Z →
      SSet.realizationWeakEquivalences ((SimplicialSpace.innerHomFunctor.map f.op).app Z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hX hY hf hZ
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff _).2 hf
  let d : CofibrantBrownFactorization f := Classical.choice inferInstance
  have ha : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.map d.i.op).app Z) :=
    (inner_precomp_trivialFibration d.i Z
      ⟨d.hi, (HomotopicalAlgebra.weakEquivalence_iff _).1 inferInstance⟩ hZ).2
  have hs : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.map d.s.op).app Z) :=
    (inner_precomp_trivialFibration d.s Z
      ⟨(HomotopicalAlgebra.cofibration_iff _).1 inferInstance,
        (HomotopicalAlgebra.weakEquivalence_iff _).1 inferInstance⟩ hZ).2
  have hps : (SimplicialSpace.innerHomFunctor.map d.p.op).app Z ≫
      (SimplicialSpace.innerHomFunctor.map d.s.op).app Z = 𝟙 _ := by
    simp only [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, ← op_comp,
      d.s_p, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
  have hp : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.map d.p.op).app Z) :=
    SSet.realizationWeakEquivalences.of_postcomp _ _ hs
      (by rw [hps]; exact SSet.realizationWeakEquivalences.id_mem _)
  rw [← d.fac, op_comp, CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hp ha

/-- Original weak arrows between fibrant targets act weakly by raw postcomposition. -/
theorem inner_postcomp_weak_of_weak (X : SimplicialSpace.{u}) {U V : SimplicialSpace.{u}}
    (g : U ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsCofibrant X → IsFibrant U → IsFibrant V → weakEquivalences SimplicialSpace.{u} g →
      SSet.realizationWeakEquivalences ((SimplicialSpace.innerHomFunctor.obj (op X)).map g) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hX hU hV hg
  let _ : IsFibrant U := hU
  let _ : IsFibrant V := hV
  let _ : WeakEquivalence g := (HomotopicalAlgebra.weakEquivalence_iff _).2 hg
  let d : FibrantBrownFactorization g := Classical.choice inferInstance
  have hp : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.obj (op X)).map d.p) :=
    (inner_postcomp_trivialFibration X d.p hX
      ⟨d.hp, (HomotopicalAlgebra.weakEquivalence_iff _).1 inferInstance⟩).2
  have hr : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.obj (op X)).map d.r) :=
    (inner_postcomp_trivialFibration X d.r hX
      ⟨(HomotopicalAlgebra.fibration_iff _).1 inferInstance,
        (HomotopicalAlgebra.weakEquivalence_iff _).1 inferInstance⟩).2
  have hir : (SimplicialSpace.innerHomFunctor.obj (op X)).map d.i ≫
      (SimplicialSpace.innerHomFunctor.obj (op X)).map d.r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, d.i_r, CategoryTheory.Functor.map_id]
  have hi : SSet.realizationWeakEquivalences
      ((SimplicialSpace.innerHomFunctor.obj (op X)).map d.i) :=
    SSet.realizationWeakEquivalences.of_postcomp _ _ hr
      (by rw [hir]; exact SSet.realizationWeakEquivalences.id_mem _)
  rw [← d.fac, CategoryTheory.Functor.map_comp]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hi hp

/-- Inner degree-zero precomposition is the original ordinary composite. -/
theorem inner_precomp_app_zero {A B : SimplicialSpace.{u}} (i : A ⟶ B) (Z : SimplicialSpace.{u})
    (b : B ⟶ Z) :
    ((SimplicialSpace.innerHomFunctor.map i.op).app Z).app (op ⦋0⦌)
        (SimplicialSpace.innerHomEquiv B Z b) = SimplicialSpace.innerHomEquiv A Z (i ≫ b) := by
  have h : eHomEquiv SSet.{u} b ≫ (SimplicialSpace.innerHomFunctor.map i.op).app Z =
      eHomEquiv SSet.{u} (i ≫ b) := by
    change eHomEquiv SSet.{u} b ≫ eHomWhiskerRight SSet.{u} i Z = _
    rw [SimplicialSpace.innerHom_comp, eHomWhiskerRight]
    simp only [← Category.assoc, tensorHom_def']
    rw [leftUnitor_inv_naturality]
  exact congrArg (fun a => a.app (op ⦋0⦌) PUnit.unit) h

end SimplicialSpace.ReedyModel
