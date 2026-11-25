/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Finite cofree complexes

For a complex shape `c` and a coefficient family `I`, the cofree complex
has terms `I i ⊞ I (c.next i)`. Its differential carries the second
coefficient to the first coefficient of the next term.

When every index has an outgoing arrow, a map to the cofree complex is
determined by its first coefficients. Injective coefficient objects give
an injective complex. Degreewise injective covers therefore supply enough
injectives in the category of complexes, using only binary biproducts.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical

universe u v w

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {ι : Type w} {c : ComplexShape ι}

/-- The finite cofree complex on a coefficient family. -/
def injectiveCofree (I : ι → A) : HomologicalComplex A c where
  X i := I i ⊞ I (c.next i)
  d i j := if hij : c.Rel i j then
    (biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) ≫
      eqToHom (congrArg I (c.next_eq' hij)) ≫
        (biprod.inl : I j ⟶ I j ⊞ I (c.next j)) else 0
  shape i j hij := by simp only [dif_neg hij]
  d_comp_d' i j k hij hjk := by
    simp only [dif_pos hij, dif_pos hjk, Category.assoc,
      biprod.inl_snd_assoc, comp_zero, zero_comp]

/-- The cofree differential includes the canonical transport of the next index. -/
theorem injectiveCofree_d (I : ι → A) {i j : ι} (hij : c.Rel i j) :
    (injectiveCofree (c := c) I).d i j =
      (biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) ≫
        eqToHom (congrArg I (c.next_eq' hij)) ≫
          (biprod.inl : I j ⟶ I j ⊞ I (c.next j)) := by
  exact dif_pos hij

/-- At the native next index, the cofree differential is second projection then insertion. -/
theorem injectiveCofree_d_next (I : ι → A) (i : ι) (hi : c.Rel i (c.next i)) :
    (injectiveCofree (c := c) I).d i (c.next i) =
      (biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) ≫
        (biprod.inl : I (c.next i) ⟶ I (c.next i) ⊞ I (c.next (c.next i))) := by
  let p : (injectiveCofree (c := c) I).X i ⟶ I (c.next i) := biprod.snd
  let q : I (c.next i) ⟶ (injectiveCofree (c := c) I).X (c.next i) := biprod.inl
  have ht : eqToHom (congrArg I (c.next_eq' hi)) = 𝟙 (I (c.next i)) := rfl
  change (injectiveCofree (c := c) I).d i (c.next i) = p ≫ q
  calc
    _ = p ≫ eqToHom (congrArg I (c.next_eq' hi)) ≫ q := injectiveCofree_d I hi
    _ = p ≫ 𝟙 _ ≫ q := congrArg (fun t => p ≫ t ≫ q) ht
    _ = p ≫ q := congrArg (fun t => p ≫ t) (Category.id_comp q)

/-- A coefficient family determines its cofree complex map. -/
def injectiveCofreeHom (K : HomologicalComplex A c) (I : ι → A)
    (a : ∀ i, K.X i ⟶ I i) : K ⟶ injectiveCofree (c := c) I where
  f i := biprod.lift (a i) (K.d i (c.next i) ≫ a (c.next i))
  comm' i j hij := by
    obtain rfl := c.next_eq' hij
    have hcomm {X Y Z B D E : A} (d : X ⟶ Y) (e : Y ⟶ Z)
        (a₀ : X ⟶ B) (a₁ : Y ⟶ D) (a₂ : Z ⟶ E) (hde : d ≫ e = 0) :
        biprod.lift a₀ (d ≫ a₁) ≫
            ((biprod.snd : B ⊞ D ⟶ D) ≫ (biprod.inl : D ⟶ D ⊞ E)) =
          d ≫ biprod.lift a₁ (e ≫ a₂) := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.inl_fst, Category.comp_id,
          biprod.lift_snd, biprod.lift_fst]
      · simp only [Category.assoc, biprod.inl_snd, comp_zero, biprod.lift_snd]
        simp only [← Category.assoc, hde, zero_comp]
    calc
      _ = biprod.lift (a i) (K.d i (c.next i) ≫ a (c.next i)) ≫
          ((biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) ≫
            (biprod.inl : I (c.next i) ⟶
              I (c.next i) ⊞ I (c.next (c.next i)))) :=
        congrArg (fun t => biprod.lift (a i)
          (K.d i (c.next i) ≫ a (c.next i)) ≫ t) (injectiveCofree_d_next I i hij)
      _ = _ := hcomm (K.d i (c.next i)) (K.d (c.next i) (c.next (c.next i)))
        (a i) (a (c.next i)) (a (c.next (c.next i)))
        (K.d_comp_d i (c.next i) (c.next (c.next i)))

/-- The first coefficient of the cofree map is the prescribed coefficient. -/
@[reassoc]
theorem injectiveCofreeHom_fst (K : HomologicalComplex A c) (I : ι → A)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (injectiveCofreeHom K I a).f i ≫
      (biprod.fst : I i ⊞ I (c.next i) ⟶ I i) = a i :=
  biprod.lift_fst _ _

/-- The second coefficient of the cofree map is obtained from the source differential. -/
@[reassoc]
theorem injectiveCofreeHom_snd (K : HomologicalComplex A c) (I : ι → A)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (injectiveCofreeHom K I a).f i ≫
      (biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) =
        K.d i (c.next i) ≫ a (c.next i) :=
  biprod.lift_snd _ _

/-- Every cofree map has its second coefficient forced at an outgoing index. -/
@[reassoc]
theorem injectiveCofree_snd (K : HomologicalComplex A c) (I : ι → A)
    (g : K ⟶ injectiveCofree (c := c) I) (i : ι) (hi : c.Rel i (c.next i)) :
    g.f i ≫ (biprod.snd : I i ⊞ I (c.next i) ⟶ I (c.next i)) =
      K.d i (c.next i) ≫ g.f (c.next i) ≫
        (biprod.fst : I (c.next i) ⊞ I (c.next (c.next i)) ⟶ I (c.next i)) := by
  let D := injectiveCofree (c := c) I
  let p : D.X i ⟶ I (c.next i) := biprod.snd
  let q : I (c.next i) ⟶ D.X (c.next i) := biprod.inl
  let r : D.X (c.next i) ⟶ I (c.next i) := biprod.fst
  have hqr : q ≫ r = 𝟙 (I (c.next i)) := biprod.inl_fst
  have hp : (g.f i ≫ (p ≫ q)) ≫ r = g.f i ≫ p :=
    (Category.assoc (g.f i) (p ≫ q) r).trans
      ((congrArg (fun t => g.f i ≫ t) (Category.assoc p q r)).trans
        ((congrArg (fun t => g.f i ≫ (p ≫ t)) hqr).trans
          (congrArg (fun t => g.f i ≫ t) (Category.comp_id p))))
  calc
    _ = (g.f i ≫ (p ≫ q)) ≫ r := hp.symm
    _ = (g.f i ≫ D.d i (c.next i)) ≫ r :=
      congrArg (fun t => (g.f i ≫ t) ≫ r) (injectiveCofree_d_next I i hi).symm
    _ = (K.d i (c.next i) ≫ g.f (c.next i)) ≫ r :=
      congrArg (fun t => t ≫ r) (g.comm i (c.next i))
    _ = _ := Category.assoc (K.d i (c.next i)) (g.f (c.next i)) r

/-- First coefficients determine maps to a cofree complex when every index is outgoing. -/
theorem injectiveCofree_hom_ext (I : ι → A) (hc : ∀ i, c.Rel i (c.next i))
    {K : HomologicalComplex A c} {f g : K ⟶ injectiveCofree (c := c) I}
    (h : ∀ i, f.f i ≫ biprod.fst = g.f i ≫ biprod.fst) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply biprod.hom_ext
  · exact h i
  · calc
      _ = K.d i (c.next i) ≫ f.f (c.next i) ≫
          (biprod.fst : I (c.next i) ⊞ I (c.next (c.next i)) ⟶ I (c.next i)) :=
        injectiveCofree_snd K I f i (hc i)
      _ = K.d i (c.next i) ≫ g.f (c.next i) ≫
          (biprod.fst : I (c.next i) ⊞ I (c.next (c.next i)) ⟶ I (c.next i)) :=
        congrArg (fun t : K.X (c.next i) ⟶ I (c.next i) => K.d i (c.next i) ≫ t)
          (h (c.next i))
      _ = _ := (injectiveCofree_snd K I g i (hc i)).symm

/-- The universal coefficient equivalence for the finite cofree complex. -/
def injectiveCofreeHomEquiv (K : HomologicalComplex A c) (I : ι → A)
    (hc : ∀ i, c.Rel i (c.next i)) :
    (K ⟶ injectiveCofree (c := c) I) ≃ (∀ i, K.X i ⟶ I i) where
  toFun g i := g.f i ≫ biprod.fst
  invFun a := injectiveCofreeHom K I a
  left_inv g := by
    apply injectiveCofree_hom_ext I hc
    intro i
    exact injectiveCofreeHom_fst K I _ i
  right_inv a := funext fun i => injectiveCofreeHom_fst K I a i

/-- Cofree maps commute with precomposition by a complex map. -/
@[reassoc]
theorem injectiveCofreeHom_precomp {K L : HomologicalComplex A c} (g : K ⟶ L)
    (I : ι → A) (a : ∀ i, L.X i ⟶ I i) :
    g ≫ injectiveCofreeHom L I a =
      injectiveCofreeHom K I (fun i => g.f i ≫ a i) := by
  apply HomologicalComplex.hom_ext
  intro i
  let D := injectiveCofree (c := c) I
  let φ : L ⟶ D := injectiveCofreeHom L I a
  let ψ : K ⟶ D := injectiveCofreeHom K I (fun j => g.f j ≫ a j)
  let p : D.X i ⟶ I i := biprod.fst
  let q : D.X i ⟶ I (c.next i) := biprod.snd
  have hφp : φ.f i ≫ p = a i := injectiveCofreeHom_fst L I a i
  have hψp : ψ.f i ≫ p = g.f i ≫ a i :=
    injectiveCofreeHom_fst K I (fun j => g.f j ≫ a j) i
  have hφq : φ.f i ≫ q = L.d i (c.next i) ≫ a (c.next i) :=
    injectiveCofreeHom_snd L I a i
  have hψq : ψ.f i ≫ q = K.d i (c.next i) ≫ g.f (c.next i) ≫ a (c.next i) :=
    injectiveCofreeHom_snd K I (fun j => g.f j ≫ a j) i
  apply biprod.hom_ext
  · calc
      _ = (g.f i ≫ φ.f i) ≫ p :=
        congrArg (fun t => t ≫ p) (HomologicalComplex.comp_f g φ i)
      _ = g.f i ≫ (φ.f i ≫ p) := Category.assoc (g.f i) (φ.f i) p
      _ = g.f i ≫ a i := congrArg (fun t => g.f i ≫ t) hφp
      _ = _ := hψp.symm
  · calc
      _ = (g.f i ≫ φ.f i) ≫ q :=
        congrArg (fun t => t ≫ q) (HomologicalComplex.comp_f g φ i)
      _ = g.f i ≫ (φ.f i ≫ q) := Category.assoc (g.f i) (φ.f i) q
      _ = g.f i ≫ L.d i (c.next i) ≫ a (c.next i) :=
        congrArg (fun t => g.f i ≫ t) hφq
      _ = K.d i (c.next i) ≫ g.f (c.next i) ≫ a (c.next i) :=
        g.comm_assoc i (c.next i) (a (c.next i))
      _ = _ := hψq.symm

/-- A family of coefficient morphisms induces its cofree map. -/
def injectiveCofreeMap {I J : ι → A} (a : ∀ i, I i ⟶ J i) :
    injectiveCofree (c := c) I ⟶ injectiveCofree (c := c) J :=
  injectiveCofreeHom (injectiveCofree (c := c) I) J (fun i => biprod.fst ≫ a i)

/-- Cofree coefficient maps commute with a prescribed coefficient family. -/
@[reassoc]
theorem injectiveCofreeHom_naturality (K : HomologicalComplex A c) {I J : ι → A}
    (hc : ∀ i, c.Rel i (c.next i)) (a : ∀ i, K.X i ⟶ I i) (b : ∀ i, I i ⟶ J i) :
    injectiveCofreeHom K I a ≫ injectiveCofreeMap b =
      injectiveCofreeHom K J (fun i => a i ≫ b i) := by
  apply injectiveCofree_hom_ext J hc
  intro i
  let D := injectiveCofree (c := c) I
  let E := injectiveCofree (c := c) J
  let φ : K ⟶ D := injectiveCofreeHom K I a
  let β : D ⟶ E := injectiveCofreeMap b
  let ψ : K ⟶ E := injectiveCofreeHom K J (fun j => a j ≫ b j)
  let p : D.X i ⟶ I i := biprod.fst
  let q : E.X i ⟶ J i := biprod.fst
  have hφ : φ.f i ≫ p = a i := injectiveCofreeHom_fst K I a i
  have hβ : β.f i ≫ q = p ≫ b i :=
    injectiveCofreeHom_fst D J (fun j => biprod.fst ≫ b j) i
  have hψ : ψ.f i ≫ q = a i ≫ b i :=
    injectiveCofreeHom_fst K J (fun j => a j ≫ b j) i
  calc
    _ = (φ.f i ≫ β.f i) ≫ q :=
      congrArg (fun t => t ≫ q) (HomologicalComplex.comp_f φ β i)
    _ = φ.f i ≫ (β.f i ≫ q) := Category.assoc (φ.f i) (β.f i) q
    _ = φ.f i ≫ (p ≫ b i) := congrArg (fun t => φ.f i ≫ t) hβ
    _ = (φ.f i ≫ p) ≫ b i := (Category.assoc (φ.f i) p (b i)).symm
    _ = a i ≫ b i := congrArg (fun t => t ≫ b i) hφ
    _ = _ := hψ.symm

/-- A finite cofree complex of injective coefficient objects is injective. -/
theorem injectiveCofree_injective (I : ι → A) (hc : ∀ i, c.Rel i (c.next i))
    [∀ i, Injective (I i)] : Injective (injectiveCofree (c := c) I) where
  factors {X Y} g m hm := by
    letI : Mono m := hm
    let a : ∀ i, Y.X i ⟶ I i := fun i =>
      Injective.factorThru (g.f i ≫ biprod.fst) (m.f i)
    refine ⟨injectiveCofreeHom Y I a, ?_⟩
    apply injectiveCofree_hom_ext I hc
    intro i
    let D := injectiveCofree (c := c) I
    let φ : Y ⟶ D := injectiveCofreeHom Y I a
    let p : D.X i ⟶ I i := biprod.fst
    have hφ : φ.f i ≫ p = a i := injectiveCofreeHom_fst Y I a i
    calc
      _ = (m.f i ≫ φ.f i) ≫ p :=
        congrArg (fun t => t ≫ p) (HomologicalComplex.comp_f m φ i)
      _ = m.f i ≫ (φ.f i ≫ p) := Category.assoc (m.f i) (φ.f i) p
      _ = m.f i ≫ a i := congrArg (fun t => m.f i ≫ t) hφ
      _ = g.f i ≫ p := Injective.comp_factorThru (g.f i ≫ p) (m.f i)

/-- Monic first coefficients give a monic cofree complex map. -/
theorem injectiveCofreeHom_mono (K : HomologicalComplex A c) (I : ι → A)
    (a : ∀ i, K.X i ⟶ I i) [∀ i, Mono (a i)] : Mono (injectiveCofreeHom K I a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact mono_of_mono_fac (injectiveCofreeHom_fst K I a i)

/-- Injective covers give enough injectives for a shape with an outgoing arrow at every index. -/
theorem enoughInjectives_of_rel_next (hc : ∀ i, c.Rel i (c.next i))
    [EnoughInjectives A] : EnoughInjectives (HomologicalComplex A c) where
  presentation K := by
    let I : ι → A := fun i => Injective.under (K.X i)
    let a : ∀ i, K.X i ⟶ I i := fun i => Injective.ι (K.X i)
    letI : ∀ i, Injective (I i) := fun i => by dsimp only [I]; infer_instance
    letI : ∀ i, Mono (a i) := fun i => by dsimp only [a, I]; infer_instance
    letI : Injective (injectiveCofree (c := c) I) := injectiveCofree_injective I hc
    letI : Mono (injectiveCofreeHom K I a) := injectiveCofreeHom_mono K I a
    exact ⟨{ J := injectiveCofree (c := c) I, f := injectiveCofreeHom K I a }⟩

end HomologicalComplex
