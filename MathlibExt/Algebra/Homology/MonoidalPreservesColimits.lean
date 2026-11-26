/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v' u'

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [hzero : HasZeroObject C] [HasFiniteColimits C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  [hcoprodLeft : ∀ Z : C, PreservesFiniteCoproducts (tensorLeft Z)]
  [hcoprodRight : ∀ Z : C, PreservesFiniteCoproducts (tensorRight Z)]

private abbrev tensorTotalFiber (n : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {n}

private theorem tensorTotalFiberFinite (n : ℕ) : Finite (tensorTotalFiber n) := by
  let f : tensorTotalFiber n → Fin (n + 1) := fun x ↦
    ⟨x.val.1, by
      have hx := x.property
      change x.val.1 + x.val.2 = n at hx
      omega⟩
  exact Finite.of_injective f (by
    rintro ⟨⟨xp, xq⟩, hx⟩ ⟨⟨yp, yq⟩, hy⟩ hxy
    change xp + xq = n at hx
    change yp + yq = n at hy
    dsimp [f] at hxy
    have hp : xp = yp := congrArg Fin.val hxy
    apply Subtype.ext
    apply Prod.ext
    · exact hp
    · change xq = yq
      omega)

attribute [local instance] tensorTotalFiberFinite
private noncomputable def tensorLeftDegreePieces
    (K : ChainComplex C ℕ) (n : ℕ) :
    ChainComplex C ℕ ⥤ Discrete (tensorTotalFiber n) ⥤ C where
  obj L :=
    { obj := fun ij ↦ K.X ij.as.val.1 ⊗ L.X ij.as.val.2
      map := fun f ↦ eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij ↦ K.X ij.as.val.1 ◁ f.f ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorLeftEvalIso (K : ChainComplex C ℕ) (n : ℕ) :
    tensorLeft K ⋙ eval C (ComplexShape.down ℕ) n ≅
      tensorLeftDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by rfl)) (fun {X Y} f ↦ by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorLeftDegreePieces]
    simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl)

section Left

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J C]
  [∀ Z : C, PreservesColimitsOfShape J (tensorLeft Z)]

private noncomputable instance tensorLeftDegreePieces_preservesColimitsOfShape
    (K : ChainComplex C ℕ) (n : ℕ) :
    PreservesColimitsOfShape J (tensorLeftDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i ↦ by
    change PreservesColimitsOfShape J
      (eval C (ComplexShape.down ℕ) i.as.val.2 ⋙ tensorLeft (K.X i.as.val.1))
    infer_instance)

/-- Let `C` be preadditive and monoidal with a zero object and
finite colimits. Suppose tensor is additive in both variables and
both left and right tensoring preserve finite coproducts. Let `J`
be a category and `C` have colimits of shape `J`. If every left tensor functor `A ⊗ -` on `C` preserves
`J`-colimits, then for any nonnegative chain complex `K`, left
tensoring `K ⊗ -` on chain complexes also preserves `J`-colimits. -/
noncomputable instance tensorLeft_preservesColimitsOfShape
    (K : ChainComplex C ℕ) :
    PreservesColimitsOfShape J (tensorLeft K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorLeftEvalIso K n).symm

end Left

private noncomputable def tensorRightDegreePieces
    (K : ChainComplex C ℕ) (n : ℕ) :
    ChainComplex C ℕ ⥤ Discrete (tensorTotalFiber n) ⥤ C where
  obj L :=
    { obj := fun ij ↦ L.X ij.as.val.1 ⊗ K.X ij.as.val.2
      map := fun f ↦ eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij ↦ f.f ij.as.val.1 ▷ K.X ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorRightEvalIso (K : ChainComplex C ℕ) (n : ℕ) :
    tensorRight K ⋙ eval C (ComplexShape.down ℕ) n ≅
      tensorRightDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ ↦ eqToIso (by rfl)) (fun {X Y} f ↦ by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorRightDegreePieces]
    simp only [MonoidalCategory.whiskerLeft_id]
    rw [Category.id_comp]
    rfl)

section Right

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J C]
  [∀ Z : C, PreservesColimitsOfShape J (tensorRight Z)]

private noncomputable instance tensorRightDegreePieces_preservesColimitsOfShape
    (K : ChainComplex C ℕ) (n : ℕ) :
    PreservesColimitsOfShape J (tensorRightDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i ↦ by
    change PreservesColimitsOfShape J
      (eval C (ComplexShape.down ℕ) i.as.val.1 ⋙ tensorRight (K.X i.as.val.2))
    infer_instance)

/-- Let `C` be preadditive and monoidal with a zero object and
finite colimits. Suppose tensor is additive in both variables and
both left and right tensoring preserve finite coproducts. Let `J`
be a category and `C` have colimits of shape `J`. If every right tensor functor `- ⊗ A` on `C` preserves
`J`-colimits, then for any nonnegative chain complex `K`, right
tensoring `- ⊗ K` on chain complexes also preserves `J`-colimits. -/
noncomputable instance tensorRight_preservesColimitsOfShape
    (K : ChainComplex C ℕ) :
    PreservesColimitsOfShape J (tensorRight K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorRightEvalIso K n).symm

end Right

end HomologicalComplex
