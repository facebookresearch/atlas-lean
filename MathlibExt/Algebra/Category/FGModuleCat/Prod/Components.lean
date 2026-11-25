/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Prod.EmbeddingComponents
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finitely generated `e`- and `f`-components for `FGModuleCat (R × S)`

For `R × S` with complementary central idempotents `e = (1,0)` and `f = (0,1)`, every
`(R × S)`-module splits into its `e`- and `f`-submodules. This file shows that when the
ambient module is finite, its `e`/`f` submodules remain finite as `(R × S)`-modules and
hence finite as `R`- and `S`-modules, lifts the component functors to `FGModuleCat`, and
provides simp API for their objects and maps together with additive instances.
-/

@[expose] public section

open CategoryTheory

universe v uR uS

namespace ProdIdempotent

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {M : Type v} [AddCommGroup M] [Module (R × S) M]

section FiniteLemmas

/-- `e`-smul after an ambient smul factors through the fst coordinate. -/
lemma eEnd_smul_eq_fst_smul (c : R × S) (m : M) :
    e R S • (c • m) = (c.1, (0 : S)) • m := by
  calc
    e R S • (c • m) = (e R S * c) • m := by rw [mul_smul]
    _ = (c.1, (0 : S)) • m := by rw [e_mul_eq]

/-- `f`-smul after an ambient smul factors through the snd coordinate. -/
lemma fEnd_smul_eq_snd_smul (c : R × S) (m : M) :
    f R S • (c • m) = ((0 : R), c.2) • m := by
  calc
    f R S • (c • m) = (f R S * c) • m := by rw [mul_smul]
    _ = ((0 : R), c.2) • m := by rw [f_mul_eq]

/-- `(r,0)`-smul factors through `e`-projection. -/
lemma fst_smul_eq_smul_eProj_val (r : R) (m : M) :
    (r, (0 : S)) • m = (r, (0 : S)) • (e R S • m) := by
  calc
    (r, (0 : S)) • m = (((r, (0 : S)) * e R S) • m) := by rw [mul_e_eq]
    _ = (r, (0 : S)) • (e R S • m) := by rw [mul_smul]

/-- `(0,s)`-smul factors through `f`-projection. -/
lemma snd_smul_eq_smul_fProj_val (s : S) (m : M) :
    ((0 : R), s) • m = ((0 : R), s) • (f R S • m) := by
  calc
    ((0 : R), s) • m = ((((0 : R), s) * f R S) • m) := by rw [mul_f_eq]
    _ = ((0 : R), s) • (f R S • m) := by rw [mul_smul]

/-- Value of `eProj (c • m)` is `(c.1,0)`-smul. -/
lemma eProj_val_fst_smul (c : R × S) (m : M) :
    (eProj (R := R) (S := S) (M := M) (c • m)).val = (c.1, (0 : S)) • m :=
  eEnd_smul_eq_fst_smul c m

/-- Value of `fProj (c • m)` is `(0,c.2)`-smul. -/
lemma fProj_val_snd_smul (c : R × S) (m : M) :
    (fProj (R := R) (S := S) (M := M) (c • m)).val = ((0 : R), c.2) • m :=
  fEnd_smul_eq_snd_smul c m

/-- `eProj` commutes with `(R × S)`-smul up to `R`-smul on the component. -/
lemma eProj_smul_eq_R_smul (c : R × S) (m : M) :
    eProj (R := R) (S := S) (M := M) (c • m) = c.1 • eProj (R := R) (S := S) m := by
  apply Subtype.ext
  calc
    (eProj (c • m)).val = (c.1, (0 : S)) • m := eProj_val_fst_smul c m
    _ = (c.1, (0 : S)) • (e R S • m) := fst_smul_eq_smul_eProj_val c.1 m
    _ = (c.1 • eProj m).val := rfl

/-- `fProj` commutes with `(R × S)`-smul up to `S`-smul on the component. -/
lemma fProj_smul_eq_S_smul (c : R × S) (m : M) :
    fProj (R := R) (S := S) (M := M) (c • m) = c.2 • fProj (R := R) (S := S) m := by
  apply Subtype.ext
  calc
    (fProj (c • m)).val = ((0 : R), c.2) • m := fProj_val_snd_smul c m
    _ = ((0 : R), c.2) • (f R S • m) := snd_smul_eq_smul_fProj_val c.2 m
    _ = (c.2 • fProj m).val := rfl

/-- `eProj` is retraction on its submodule. -/
lemma eProj_of_mem (x : eSubmodule (R := R) (S := S) (M := M)) :
    eProj (R := R) (S := S) x.val = x := by
  apply Subtype.ext
  exact e_smul_of_mem_eSubmodule x.2

/-- `fProj` is retraction on its submodule. -/
lemma fProj_of_mem (y : fSubmodule (R := R) (S := S) (M := M)) :
    fProj (R := R) (S := S) y.val = y := by
  apply Subtype.ext
  exact f_smul_of_mem_fSubmodule y.2

/-- `eProj` is surjective onto its submodule. -/
lemma eProj_surjective :
    Function.Surjective (eProj (R := R) (S := S) (M := M)) := fun x =>
  ⟨x.val, eProj_of_mem x⟩

/-- `fProj` is surjective onto its submodule. -/
lemma fProj_surjective :
    Function.Surjective (fProj (R := R) (S := S) (M := M)) := fun y =>
  ⟨y.val, fProj_of_mem y⟩

/-- `(R × S)`-smul on `eSubmodule` coincides with `R`-smul via fst. -/
lemma eSubmodule_smul_eq_R_smul (c : R × S)
    (x : eSubmodule (R := R) (S := S) (M := M)) :
    (c • x : eSubmodule (R := R) (S := S) (M := M)) = c.1 • x := by
  apply Subtype.ext
  calc
    (c • x).val = c • x.val := rfl
    _ = (c.1, (0 : S)) • x.val := smul_eq_fst_smul_of_mem_eSubmodule x.2 c
    _ = (c.1 • x).val := rfl

/-- `(R × S)`-smul on `fSubmodule` coincides with `S`-smul via snd. -/
lemma fSubmodule_smul_eq_S_smul (c : R × S)
    (y : fSubmodule (R := R) (S := S) (M := M)) :
    (c • y : fSubmodule (R := R) (S := S) (M := M)) = c.2 • y := by
  apply Subtype.ext
  calc
    (c • y).val = c • y.val := rfl
    _ = ((0 : R), c.2) • y.val := smul_eq_snd_smul_of_mem_fSubmodule y.2 c
    _ = (c.2 • y).val := rfl

end FiniteLemmas

section FinitePreservation

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {M : Type v} [AddCommGroup M] [Module (R × S) M]

/-- Finite `(R × S)`-module gives finite `e`-submodule as `(R × S)`-module. -/
lemma finite_eSubmodule_of_finite (hM : Module.Finite (R × S) M) :
    Module.Finite (R × S) (eSubmodule (R := R) (S := S) (M := M)) :=
  Module.Finite.of_surjective (eProj (R := R) (S := S)) eProj_surjective

/-- Finite `(R × S)`-module gives finite `f`-submodule as `(R × S)`-module. -/
lemma finite_fSubmodule_of_finite (hM : Module.Finite (R × S) M) :
    Module.Finite (R × S) (fSubmodule (R := R) (S := S) (M := M)) :=
  Module.Finite.of_surjective (fProj (R := R) (S := S)) fProj_surjective

/-- Finite `(R × S)`-module gives finite `e`-component as `R`-module. -/
lemma finite_R_eSubmodule_of_finite (hM : Module.Finite (R × S) M) :
    Module.Finite R (eSubmodule (R := R) (S := S) (M := M)) := by
  classical
  have hFinRS : Module.Finite (R × S) (eSubmodule (R := R) (S := S) (M := M)) :=
    finite_eSubmodule_of_finite hM
  rw [Module.finite_def] at hFinRS ⊢
  obtain ⟨t, ht⟩ := hFinRS
  refine ⟨t, ?_⟩
  let S_R : Submodule R (eSubmodule (R := R) (S := S) (M := M)) :=
    Submodule.span R (↑t : Set _)
  let S_RS : Submodule (R × S) (eSubmodule (R := R) (S := S) (M := M)) :=
    { carrier := ↑S_R
      add_mem' := fun {a b} ha hb => S_R.add_mem ha hb
      zero_mem' := S_R.zero_mem
      smul_mem' := fun c y hy => by
        have : (c • y : eSubmodule (R := R) (S := S) (M := M)) = c.1 • y :=
          eSubmodule_smul_eq_R_smul c y
        rw [this]
        exact S_R.smul_mem c.1 hy }
  have h_span_le : Submodule.span (R × S) (↑t : Set _) ≤ S_RS := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.mem_span_of_mem hx
  rw [ht] at h_span_le
  have h_top_le : (⊤ : Submodule (R × S) _) ≤ S_RS := h_span_le
  have h_S_R_top : S_R = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ S_RS := h_top_le Submodule.mem_top
    exact hx
  exact h_S_R_top

/-- Finite `(R × S)`-module gives finite `f`-component as `S`-module. -/
lemma finite_S_fSubmodule_of_finite (hM : Module.Finite (R × S) M) :
    Module.Finite S (fSubmodule (R := R) (S := S) (M := M)) := by
  classical
  have hFinRS : Module.Finite (R × S) (fSubmodule (R := R) (S := S) (M := M)) :=
    finite_fSubmodule_of_finite hM
  rw [Module.finite_def] at hFinRS ⊢
  obtain ⟨t, ht⟩ := hFinRS
  refine ⟨t, ?_⟩
  let S_S : Submodule S (fSubmodule (R := R) (S := S) (M := M)) :=
    Submodule.span S (↑t : Set _)
  let S_RS : Submodule (R × S) (fSubmodule (R := R) (S := S) (M := M)) :=
    { carrier := ↑S_S
      add_mem' := fun {a b} ha hb => S_S.add_mem ha hb
      zero_mem' := S_S.zero_mem
      smul_mem' := fun c y hy => by
        have : (c • y : fSubmodule (R := R) (S := S) (M := M)) = c.2 • y :=
          fSubmodule_smul_eq_S_smul c y
        rw [this]
        exact S_S.smul_mem c.2 hy }
  have h_span_le : Submodule.span (R × S) (↑t : Set _) ≤ S_RS := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.mem_span_of_mem hx
  rw [ht] at h_span_le
  have h_top_le : (⊤ : Submodule (R × S) _) ≤ S_RS := h_span_le
  have h_S_S_top : S_S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ S_RS := h_top_le Submodule.mem_top
    exact hx
  exact h_S_S_top

end FinitePreservation

section FGPreservation

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- If `M` is finitely generated over `R × S`, its `e`-component is FG over `R`. -/
theorem isFG_eComponent_of_isFG (M : ModuleCat.{v} (R × S))
    (hM : ModuleCat.isFG (R × S) M) :
    ModuleCat.isFG R (eSubmoduleAsModuleCat (R := R) (S := S) M) := by
  have hFin : Module.Finite (R × S) (M : Type v) := hM
  exact finite_R_eSubmodule_of_finite hFin

/-- If `M` is finitely generated over `R × S`, its `f`-component is FG over `S`. -/
theorem isFG_fComponent_of_isFG (M : ModuleCat.{v} (R × S))
    (hM : ModuleCat.isFG (R × S) M) :
    ModuleCat.isFG S (fSubmoduleAsModuleCat (R := R) (S := S) M) := by
  have hFin : Module.Finite (R × S) (M : Type v) := hM
  exact finite_S_fSubmodule_of_finite hFin

end FGPreservation

section Functors

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Lifted `e`-component functor for finitely generated modules. -/
noncomputable def eComponentFunctorFG :
    FGModuleCat.{v} (R × S) ⥤ FGModuleCat.{v} R :=
  (ModuleCat.isFG (R := R)).lift
    (forget₂ (FGModuleCat.{v} (R × S)) (ModuleCat.{v} (R × S)) ⋙ eComponentFunctor)
    (fun X => isFG_eComponent_of_isFG (R := R) (S := S) X.obj X.property)

/-- Lifted `f`-component functor for finitely generated modules. -/
noncomputable def fComponentFunctorFG :
    FGModuleCat.{v} (R × S) ⥤ FGModuleCat.{v} S :=
  (ModuleCat.isFG (R := S)).lift
    (forget₂ (FGModuleCat.{v} (R × S)) (ModuleCat.{v} (R × S)) ⋙ fComponentFunctor)
    (fun X => isFG_fComponent_of_isFG (R := R) (S := S) X.obj X.property)

/-- Underlying `ModuleCat` of `eComponentFunctorFG.obj X`. -/
@[simp]
lemma eComponentFunctorFG_obj_obj (X : FGModuleCat.{v} (R × S)) :
    ((eComponentFunctorFG (R := R) (S := S)).obj X).obj =
      eSubmoduleAsModuleCat (R := R) (S := S) X.obj :=
  rfl

/-- Underlying `ModuleCat` of `fComponentFunctorFG.obj X`. -/
@[simp]
lemma fComponentFunctorFG_obj_obj (X : FGModuleCat.{v} (R × S)) :
    ((fComponentFunctorFG (R := R) (S := S)).obj X).obj =
      fSubmoduleAsModuleCat (R := R) (S := S) X.obj :=
  rfl

/-- Carrier type of `eComponentFunctorFG.obj X` equals the `e`-submodule. -/
@[simp]
lemma eComponentFunctorFG_obj_coe (X : FGModuleCat.{v} (R × S)) :
    ((eComponentFunctorFG (R := R) (S := S)).obj X : Type v) =
      eSubmodule (R := R) (S := S) (M := X.obj) :=
  rfl

/-- Carrier type of `fComponentFunctorFG.obj X` equals the `f`-submodule. -/
@[simp]
lemma fComponentFunctorFG_obj_coe (X : FGModuleCat.{v} (R × S)) :
    ((fComponentFunctorFG (R := R) (S := S)).obj X : Type v) =
      fSubmodule (R := R) (S := S) (M := X.obj) :=
  rfl

/-- Hom map of `eComponentFunctorFG` equals that of `eComponentFunctor`. -/
@[simp]
lemma eComponentFunctorFG_map_hom {X Y : FGModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((eComponentFunctorFG (R := R) (S := S)).map f).hom =
      (eComponentFunctor (R := R) (S := S)).map f.hom :=
  rfl

/-- Hom map of `fComponentFunctorFG` equals that of `fComponentFunctor`. -/
@[simp]
lemma fComponentFunctorFG_map_hom {X Y : FGModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((fComponentFunctorFG (R := R) (S := S)).map f).hom =
      (fComponentFunctor (R := R) (S := S)).map f.hom :=
  rfl

/-- Underlying linear map of `eComponentFunctorFG.map f`. -/
@[simp]
lemma eComponentFunctorFG_map_hom_hom {X Y : FGModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((eComponentFunctorFG (R := R) (S := S)).map f).hom.hom =
      ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom.hom :=
  rfl

/-- Underlying linear map of `fComponentFunctorFG.map f`. -/
@[simp]
lemma fComponentFunctorFG_map_hom_hom {X Y : FGModuleCat.{v} (R × S)} (f : X ⟶ Y) :
    ((fComponentFunctorFG (R := R) (S := S)).map f).hom.hom =
      ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom.hom :=
  rfl

/-- Comparison iso `eComponentFG ⋙ forget₂ ≅ forget₂ ⋙ eComponent`. -/
noncomputable def eComponentFunctorFG_comp_forget₂Iso :
    eComponentFunctorFG (R := R) (S := S) ⋙
      forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ≅
      forget₂ (FGModuleCat.{v} (R × S)) (ModuleCat.{v} (R × S)) ⋙
        eComponentFunctor (R := R) (S := S) :=
  (ModuleCat.isFG (R := R)).liftCompιIso _ _

/-- Comparison iso `fComponentFG ⋙ forget₂ ≅ forget₂ ⋙ fComponent`. -/
noncomputable def fComponentFunctorFG_comp_forget₂Iso :
    fComponentFunctorFG (R := R) (S := S) ⋙
      forget₂ (FGModuleCat.{v} S) (ModuleCat.{v} S) ≅
      forget₂ (FGModuleCat.{v} (R × S)) (ModuleCat.{v} (R × S)) ⋙
        fComponentFunctor (R := R) (S := S) :=
  (ModuleCat.isFG (R := S)).liftCompιIso _ _

/-- `eComponentFunctorFG` preserves addition. -/
instance eComponentFunctorFG_additive :
    (eComponentFunctorFG (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply FGModuleCat.hom_ext
    have h_add : (f + g).hom = f.hom + g.hom := by
      apply ModuleCat.hom_ext
      rfl
    have h_add_hom : (f + g).hom.hom = f.hom.hom + g.hom.hom := by
      rw [h_add]
      rfl
    have h_map_add : (eComponentFunctorFG.map f + eComponentFunctorFG.map g).hom =
        (eComponentFunctorFG.map f).hom + (eComponentFunctorFG.map g).hom := by
      apply ModuleCat.hom_ext
      rfl
    change (eComponentFunctorFG.map (f + g)).hom.hom =
        ((eComponentFunctorFG.map f + eComponentFunctorFG.map g).hom).hom
    have eq1 : (eComponentFunctorFG.map (f + g)).hom.hom =
        ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (f + g).hom.hom := rfl
    have eq2 : ProdIdempotent.map_eSubmodule_R (R := R) (S := S) (f + g).hom.hom =
        ProdIdempotent.map_eSubmodule_R (R := R) (S := S)
          (f.hom.hom + g.hom.hom) := by rw [h_add_hom]
    have eq3 : ProdIdempotent.map_eSubmodule_R (R := R) (S := S)
          (f.hom.hom + g.hom.hom) =
        ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom.hom +
          ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g.hom.hom :=
      map_eSubmodule_R_add _ _
    have eq4 : ProdIdempotent.map_eSubmodule_R (R := R) (S := S) f.hom.hom +
          ProdIdempotent.map_eSubmodule_R (R := R) (S := S) g.hom.hom =
        (eComponentFunctorFG.map f).hom.hom + (eComponentFunctorFG.map g).hom.hom := rfl
    have eq5 : (eComponentFunctorFG.map f).hom.hom + (eComponentFunctorFG.map g).hom.hom =
        ((eComponentFunctorFG.map f).hom + (eComponentFunctorFG.map g).hom).hom := rfl
    have eq6 : ((eComponentFunctorFG.map f).hom + (eComponentFunctorFG.map g).hom).hom =
        ((eComponentFunctorFG.map f + eComponentFunctorFG.map g).hom).hom := by
      rw [← h_map_add]
    exact eq1.trans (eq2.trans (eq3.trans (eq4.trans (eq5.trans eq6))))

/-- `fComponentFunctorFG` preserves addition. -/
instance fComponentFunctorFG_additive :
    (fComponentFunctorFG (R := R) (S := S)).Additive where
  map_add {X Y} f g := by
    apply FGModuleCat.hom_ext
    have h_add : (f + g).hom = f.hom + g.hom := by
      apply ModuleCat.hom_ext
      rfl
    have h_add_hom : (f + g).hom.hom = f.hom.hom + g.hom.hom := by
      rw [h_add]
      rfl
    have h_map_add : (fComponentFunctorFG.map f + fComponentFunctorFG.map g).hom =
        (fComponentFunctorFG.map f).hom + (fComponentFunctorFG.map g).hom := by
      apply ModuleCat.hom_ext
      rfl
    change (fComponentFunctorFG.map (f + g)).hom.hom =
        ((fComponentFunctorFG.map f + fComponentFunctorFG.map g).hom).hom
    have eq1 : (fComponentFunctorFG.map (f + g)).hom.hom =
        ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (f + g).hom.hom := rfl
    have eq2 : ProdIdempotent.map_fSubmodule_S (R := R) (S := S) (f + g).hom.hom =
        ProdIdempotent.map_fSubmodule_S (R := R) (S := S)
          (f.hom.hom + g.hom.hom) := by rw [h_add_hom]
    have eq3 : ProdIdempotent.map_fSubmodule_S (R := R) (S := S)
          (f.hom.hom + g.hom.hom) =
        ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom.hom +
          ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g.hom.hom :=
      map_fSubmodule_S_add _ _
    have eq4 : ProdIdempotent.map_fSubmodule_S (R := R) (S := S) f.hom.hom +
          ProdIdempotent.map_fSubmodule_S (R := R) (S := S) g.hom.hom =
        (fComponentFunctorFG.map f).hom.hom + (fComponentFunctorFG.map g).hom.hom := rfl
    have eq5 : (fComponentFunctorFG.map f).hom.hom + (fComponentFunctorFG.map g).hom.hom =
        ((fComponentFunctorFG.map f).hom + (fComponentFunctorFG.map g).hom).hom := rfl
    have eq6 : ((fComponentFunctorFG.map f).hom + (fComponentFunctorFG.map g).hom).hom =
        ((fComponentFunctorFG.map f + fComponentFunctorFG.map g).hom).hom := by
      rw [← h_map_add]
    exact eq1.trans (eq2.trans (eq3.trans (eq4.trans (eq5.trans eq6))))

end Functors

end ProdIdempotent
