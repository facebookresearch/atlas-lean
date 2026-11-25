/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Closed.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.InternalHom
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Tensor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Closedness of the balanced tensor product

For a commutative monoid object `A` in a braided closed monoidal category, the internal
object of `A`-linear maps is right adjoint to balanced tensoring with a module. Thus the
balanced tensor product and `Mod.internalHom` make `Mod C A` monoidal closed, provided
that equalizers and tensor-preserved coequalizers exist.

The bijection is ordinary currying on representatives. Linearity in the first variable
makes a curried map land in the equalizer of linear maps; balancing is exactly linearity
of that map in the second variable. In particular this identifies function spectra with
the internal hom for the point-set smash product, without any model-category assertion.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory.Mod

open MonoidalCategory BraidedCategory MonObj MonoidalClosed Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- Currying a map linear in its first variable gives a module map exactly when the
original map is balanced in its two variables. -/
lemma isModHom_ihomHomEquiv_iff (M K N : Mod C A)
    (f : (Mod.tensorLeft M).obj K.X ⟶ N) :
    letI := ihomModObj M N
    IsModHom A (ihomHomEquiv M K.X N f) ↔
      ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ K.X ≫ f.hom =
        (α_ M.X A K.X).hom ≫ M.X ◁ γ[A, K.X] ≫ f.hom := by
  let := ihomModObj M N
  let g := ihomHomEquiv M K.X N f
  have hg : M.X ◁ g ≫ uncurry (ihomι M N) = f.hom := by
    rw [← uncurry_natural_left, ihomHomEquiv_apply_comp_ihomι, uncurry_curry]
  have h (k : A ⊗ K.X ⟶ (ihom M).obj N) (l : A ⊗ K.X ⟶ (ihom M).obj N) :
      k = l ↔ M.X ◁ k ≫ uncurry (ihomι M N) =
        M.X ◁ l ≫ uncurry (ihomι M N) := by
    rw [← uncurry_natural_left, ← uncurry_natural_left, uncurry_injective.eq_iff,
      cancel_mono]
  have hm : IsModHom A g ↔ γ[A, K.X] ≫ g =
      A ◁ g ≫ ((internalHom M).obj N).mod.smul :=
    ⟨fun hf ↦ hf.smul_hom, fun hf ↦ ⟨hf⟩⟩
  rw [hm, h]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_internalHom_smul_comp_uncurry_ihomι,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, hg, Iso.eq_inv_comp]
  exact eq_comm

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- Balanced tensoring with `M` is left adjoint to the module of linear maps out of `M`:
the bijection is currying after precomposing with the balanced quotient. -/
noncomputable def tensorHomEquiv (M K N : Mod C A) :
    (M ⊗ K ⟶ N) ≃ (K ⟶ (internalHom M).obj N) where
  toFun f := by
    let l : (Mod.tensorLeft M).obj K.X ⟶ N := Hom.mk' (tensorπ M K ≫ f.hom) (by
      simp only [tensorLeft_smul, selfLeftAction_actionHomRight, Category.assoc]
      rw [← whiskerLeft_tensorπ_smul_assoc, IsModHom.smul_hom]
      simp)
    exact Hom.mk' (ihomHomEquiv M K.X N l)
      ((isModHom_ihomHomEquiv_iff M K N l).2 (by
        simpa only [l, Hom.mk'_hom, Category.assoc] using
          tensorπ_condition_assoc M K f.hom)).smul_hom
  invFun g := by
    let f := (ihomHomEquiv M K.X N).symm g.hom
    have hf : ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ K.X ≫ f.hom =
        (α_ M.X A K.X).hom ≫ M.X ◁ γ[A, K.X] ≫ f.hom :=
      (isModHom_ihomHomEquiv_iff M K N f).1 (by
        simpa only [f, Equiv.apply_symm_apply] using g.isModHom)
    exact Hom.mk' (tensorDesc f.hom hf) (by
      apply (cancel_epi (A ◁ tensorπ M K)).1
      simp only [selfLeftAction_actionHomRight, whiskerLeft_tensorπ_smul_assoc,
        ← whiskerLeft_comp_assoc, tensorπ_tensorDesc]
      simpa only [tensorLeft_smul, selfLeftAction_actionHomRight, Category.assoc]
        using f.isModHom.smul_hom)
  left_inv f := by
    apply Hom.ext
    apply tensor_hom_ext
    simp
  right_inv g := by
    apply Hom.ext
    apply ihom_hom_ext
    dsimp only
    simp only [Hom.mk'_hom, tensorπ_tensorDesc]
    rw [ihomHomEquiv_apply_comp_ihomι M]
    simp only [Hom.mk'_hom]
    rw [ihomHomEquiv_symm_apply_hom M, curry_uncurry]

/-- The curried module map, included into the ambient internal hom, is ordinary currying
of the map on representatives. -/
@[reassoc (attr := simp)]
lemma tensorHomEquiv_apply_hom_comp_ihomι (M K N : Mod C A) (f : M ⊗ K ⟶ N) :
    (tensorHomEquiv M K N f).hom ≫ ihomι M N = curry (tensorπ M K ≫ f.hom) := by
  dsimp only [tensorHomEquiv]
  exact ihomHomEquiv_apply_comp_ihomι M _

/-- Uncurrying a module map evaluates it on representatives of the balanced tensor. -/
@[reassoc (attr := simp)]
lemma tensorπ_tensorHomEquiv_symm_apply_hom (M K N : Mod C A)
    (g : K ⟶ (internalHom M).obj N) :
    tensorπ M K ≫ ((tensorHomEquiv M K N).symm g).hom = uncurry (g.hom ≫ ihomι M N) := by
  simp only [tensorHomEquiv, Equiv.symm, Equiv.coe_fn_mk, Hom.mk'_hom, tensorπ_tensorDesc]
  exact ihomHomEquiv_symm_apply_hom M _

/-- The balanced tensor product is left adjoint to the internal module of linear maps. -/
noncomputable def internalHomAdjunction (M : Mod C A) :
    MonoidalCategory.tensorLeft M ⊣ internalHom M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv M
      homEquiv_naturality_left_symm := by
        intro K K' N f g
        apply Hom.ext
        apply tensor_hom_ext
        rw [tensorπ_tensorHomEquiv_symm_apply_hom M K N]
        simp only [comp_hom', curriedTensor_obj_map, Category.assoc]
        rw [tensorπ_whiskerLeft_hom_assoc M f,
          tensorπ_tensorHomEquiv_symm_apply_hom M K' N, uncurry_natural_left]
      homEquiv_naturality_right := by
        intro K N N' f g
        apply Hom.ext
        apply ihom_hom_ext
        rw [tensorHomEquiv_apply_hom_comp_ihomι M K N', comp_hom']
        dsimp only [internalHom]
        simp only [comp_hom', Hom.mk'_hom, Category.assoc]
        rw [ihom_map_comp_ihomι, tensorHomEquiv_apply_hom_comp_ihomι_assoc M K N]
        simp only [curry_natural_right, Functor.map_comp, Category.assoc] }

/-- The hom-set bijection of the balanced tensor adjunction is currying on representatives. -/
@[simp]
lemma internalHomAdjunction_homEquiv (M : Mod C A) :
    (internalHomAdjunction M).homEquiv = tensorHomEquiv M :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- Modules over a commutative monoid in a braided closed monoidal category form a closed
monoidal category under balanced tensor, with the equalizer internal hom. -/
noncomputable instance monoidalClosed : MonoidalClosed (Mod C A) where
  closed M := { rightAdj := internalHom M, adj := internalHomAdjunction M }

/-- Native currying for the closed module category is the balanced tensor bijection. -/
lemma curry_eq_tensorHomEquiv (M K N : Mod C A) (f : M ⊗ K ⟶ N) :
    curry f = tensorHomEquiv M K N f := by
  rw [← homEquiv_apply_eq]
  exact congrArg (fun e ↦ e f) (congrFun (congrFun (internalHomAdjunction_homEquiv M) K) N)

/-- Evaluation for the closed module category is evaluation of linear maps on
representatives of the balanced tensor. -/
@[reassoc (attr := simp)]
lemma tensorπ_ihom_ev_app_hom (M N : Mod C A) :
    tensorπ M ((internalHom M).obj N) ≫ ((CategoryTheory.ihom.ev M).app N).hom =
      uncurry (ihomι M N) := by
  -- The closed structure chooses precisely `internalHomAdjunction`, so its counit is evaluation.
  change tensorπ M ((internalHom M).obj N) ≫ ((internalHomAdjunction M).counit.app N).hom = _
  rw [internalHomAdjunction, Adjunction.mkOfHomEquiv_counit_app,
    tensorπ_tensorHomEquiv_symm_apply_hom]
  simp

/-- Precomposition of internal module maps is ambient precomposition after inclusion. -/
@[reassoc]
lemma pre_app_hom_comp_ihomι {M M' : Mod C A} (f : M ⟶ M') (N : Mod C A) :
    ((MonoidalClosed.pre f).app N).hom ≫ ihomι M N =
      ihomι M' N ≫ (MonoidalClosed.pre f.hom).app N.X := by
  let p : (internalHom M').obj N ⟶ (internalHom M).obj N := (MonoidalClosed.pre f).app N
  -- Use the selected internal-hom module carriers before uncurrying in the base category.
  change p.hom ≫ ihomι M N = _
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  let e : M ⊗ (internalHom M).obj N ⟶ N := (CategoryTheory.ihom.ev M).app N
  let e' : M' ⊗ (internalHom M').obj N ⟶ N := (CategoryTheory.ihom.ev M').app N
  have he : tensorπ M ((internalHom M).obj N) ≫ e.hom = uncurry (ihomι M N) :=
    tensorπ_ihom_ev_app_hom M N
  have he' : tensorπ M' ((internalHom M').obj N) ≫ e'.hom = uncurry (ihomι M' N) :=
    tensorπ_ihom_ev_app_hom M' N
  have h : M ◁ p ≫ e = f ▷ (internalHom M').obj N ≫ e' :=
    id_tensor_pre_app_comp_ev f N
  have h' : (M ◁ p).hom ≫ e.hom = (f ▷ (internalHom M').obj N).hom ≫ e'.hom :=
    congrArg Hom.hom h
  calc
    _ = tensorπ M ((internalHom M').obj N) ≫ (M ◁ p).hom ≫ e.hom := by
      rw [tensorπ_whiskerLeft_hom_assoc, he]
    _ = tensorπ M ((internalHom M').obj N) ≫
        (f ▷ (internalHom M').obj N).hom ≫ e'.hom := by rw [h']
    _ = _ := by rw [tensorπ_whiskerRight_hom_assoc, he']

end CategoryTheory.Mod
