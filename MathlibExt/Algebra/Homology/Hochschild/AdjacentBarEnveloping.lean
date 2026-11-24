/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED guarded source proposal from the adjacent bar provider; original maps retained. -/
-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBar
public import Mathlib.Algebra.Azumaya.Defs
public import MathlibExt.Algebra.Homology.Hochschild.OuterWord
public import MathlibExt.Algebra.Module.TensorPowerOuterAction
public import Mathlib.Algebra.Module.ULift

/-!
# The adjacent-product bar over the enveloping algebra

The outer factors give the adjacent-product bar its enveloping-algebra
module structure. Its terms are A ⊗[k] TensorPower(k, n + 1, A), its
differential is b′ and its augmentation is multiplication into A.
-/
@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ModuleCat.Algebra.Hochschild
open scoped TensorProduct

universe u v
namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The original enveloping algebra, retaining its opposite right coordinate. -/
abbrev EnvelopingAlgebra := A ⊗[k] Aᵐᵒᵖ

/-- The native regular enveloping representation on the original algebra carrier. -/
abbrev regularEnvelopingAction : EnvelopingAlgebra k A →ₐ[k] Module.End k A :=
  AlgHom.mulLeftRight k A

private def barPure (n : ℕ) (a : Fin (n + 2) → A) : A ⊗[k] TensorPower k (n + 1) A :=
  a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)

private theorem representation_barPure (n : ℕ) (l r : A) (a : Fin (n + 2) → A) :
    TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r) (barPure k A n a) =
      barPure k A n (outerWord n l r a) := by
  have h := TensorPower.outerModule_tprod k A n l r (a 0) (Fin.tail a)
  change TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
    (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)) = _ at h
  have hlast : (Fin.tail a) (Fin.last n) = a (Fin.last (n + 1)) := rfl
  simpa only [barPure, outerWord, Fin.cons_zero, Fin.tail_cons, hlast] using h

private theorem adjacentFace_barPure (n : ℕ) (i : Fin (n + 2)) (a : Fin (n + 3) → A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom (barPure k A (n + 1) a) =
      barPure k A n (hochschildMulAdjacent i a) := by
  apply (TensorPower.consEquiv k A (n + 1)).injective
  have h := NonUnital.regularFace_cons_tprod k A (n + 1) i (a 0) (Fin.tail a)
  simpa only [barPure, TensorPower.consEquiv_tmul, Fin.cons_self_tail] using h

private theorem adjacentFace_pure_intertwines (n : ℕ) (i : Fin (n + 2)) (l r : A)
    (a : Fin (n + 3) → A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom
        (TensorPower.outerRepresentation k A (n + 1)
          (l ⊗ₜ[k] MulOpposite.op r) (barPure k A (n + 1) a)) =
      TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        ((NonUnital.regularFace k A (n + 1) i.castSucc).hom (barPure k A (n + 1) a)) := by
  let f := (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  calc
    f (TensorPower.outerRepresentation k A (n + 1)
        (l ⊗ₜ[k] MulOpposite.op r) (barPure k A (n + 1) a)) =
        f (barPure k A (n + 1) (outerWord (n + 1) l r a)) :=
      congrArg f (representation_barPure k A (n + 1) l r a)
    _ = barPure k A n (hochschildMulAdjacent i (outerWord (n + 1) l r a)) :=
      adjacentFace_barPure k A n i _
    _ = barPure k A n (outerWord n l r (hochschildMulAdjacent i a)) :=
      congrArg (barPure k A n) (mulAdjacent_outerWord n i l r a)
    _ = TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        (barPure k A n (hochschildMulAdjacent i a)) :=
      (representation_barPure k A n l r _).symm
    _ = TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        (f (barPure k A (n + 1) a)) :=
      congrArg (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r))
        (adjacentFace_barPure k A n i a).symm

/-- Each non-wrapping adjacent face intertwines the canonical outer representation. -/
theorem barAdjacentFace_intertwines (n : ℕ) (i : Fin (n + 2)) (z : EnvelopingAlgebra k A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom.comp
        (TensorPower.outerRepresentation k A (n + 1) z) =
      (TensorPower.outerRepresentation k A n z).comp
        (NonUnital.regularFace k A (n + 1) i.castSucc).hom := by
  let f : (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k]
      A ⊗[k] TensorPower k (n + 1) A :=
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  induction z using TensorProduct.inductionOn with
  | tmul l r =>
      apply tensorPower_ext
        (f := f.comp (TensorPower.outerRepresentation k A (n + 1) (l ⊗ₜ[k] r)))
        (g := (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] r)).comp f)
      intro a₀ a
      have hp := adjacentFace_pure_intertwines k A n i l r.unop (Fin.cons a₀ a)
      simpa only [LinearMap.comp_apply, barPure, Fin.cons_zero, Fin.tail_cons,
        MulOpposite.op_unop, f] using hp
  | add z w hz hw =>
      apply LinearMap.ext
      intro x
      simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using
        congrArg₂ (· + ·) (DFunLike.congr_fun hz x) (DFunLike.congr_fun hw x)

/-- The original signed adjacent-product boundary is enveloping-linear. -/
theorem underlyingBarBoundary_intertwines (n : ℕ) (z : EnvelopingAlgebra k A) :
    ((underlyingBar k A).d (n + 1) n).hom.comp
        (TensorPower.outerRepresentation k A (n + 1) z) =
      (TensorPower.outerRepresentation k A n z).comp
        ((underlyingBar k A).d (n + 1) n).hom := by
  let D : (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k] (A ⊗[k] TensorPower k (n + 1) A) :=
    ((underlyingBar k A).d (n + 1) n).hom
  let F : Fin (n + 2) →
      (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k] (A ⊗[k] TensorPower k (n + 1) A) :=
    fun i => (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  have hd : D = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F i := by
    have hs := ModuleCat.hom_sum (R := k)
      (M := NonUnital.chainLevel k A A (n + 2))
      (N := NonUnital.chainLevel k A A (n + 1))
      (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val •
        NonUnital.regularFace k A (n + 1) i.castSucc) Finset.univ
    have hs' :
        ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          NonUnital.regularFace k A (n + 1) i.castSucc) :
          NonUnital.chainLevel k A A (n + 2) ⟶ NonUnital.chainLevel k A A (n + 1)).hom =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F i := by
      simpa only [ModuleCat.hom_zsmul, F] using hs
    exact (congrArg (fun f : (underlyingBar k A).X (n + 1) ⟶
      (underlyingBar k A).X n => f.hom) (underlyingBar_d k A n)).trans hs'
  apply LinearMap.ext
  intro x
  change D (TensorPower.outerRepresentation k A (n + 1) z x) =
    TensorPower.outerRepresentation k A n z (D x)
  rw [hd]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun y => ((-1 : ℤ) ^ i.val) • y)
    (DFunLike.congr_fun (barAdjacentFace_intertwines k A n i z) x)

/-- Add only enveloping-linearity to the exact boundary function. -/
def envelopingBoundaryLinear (n : ℕ) :
    letI := TensorPower.outerModule k A (n + 1)
    letI := TensorPower.outerModule k A n
    (A ⊗[k] TensorPower k (n + 2) A) →ₗ[EnvelopingAlgebra k A]
      (A ⊗[k] TensorPower k (n + 1) A) := by
  let := TensorPower.outerModule k A (n + 1)
  let := TensorPower.outerModule k A n
  exact {
    toFun := ((underlyingBar k A).d (n + 1) n).hom
    map_add' := ((underlyingBar k A).d (n + 1) n).hom.map_add
    map_smul' := fun z x => by
      change ((underlyingBar k A).d (n + 1) n).hom
        (TensorPower.outerRepresentation k A (n + 1) z x) =
          TensorPower.outerRepresentation k A n z
            (((underlyingBar k A).d (n + 1) n).hom x)
      exact DFunLike.congr_fun (underlyingBarBoundary_intertwines k A n z) x }

/-- The original degree-n carrier with its left enveloping module. -/
def envelopingBarDegree (n : ℕ) : ModuleCat.{max u v} (EnvelopingAlgebra k A) := by
  let := TensorPower.outerModule k A n
  exact ModuleCat.of (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 1) A)

/-- The categorical differential has precisely the original boundary function. -/
def envelopingBarBoundary (n : ℕ) : envelopingBarDegree k A (n + 1) ⟶ envelopingBarDegree k A n := by
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 2) A) :=
    TensorPower.outerModule k A (n + 1)
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 1) A) :=
    TensorPower.outerModule k A n
  exact ModuleCat.ofHom (envelopingBoundaryLinear k A n)

/-- Its square is zero by the already underlying-bar square, not a replacement formula. -/
theorem envelopingBarBoundary_square (n : ℕ) :
    envelopingBarBoundary k A (n + 1) ≫ envelopingBarBoundary k A n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  change ((underlyingBar k A).d (n + 1) n).hom
    (((underlyingBar k A).d (n + 2) (n + 1)).hom x) = 0
  have h := ConcreteCategory.congr_hom
    ((underlyingBar k A).d_comp_d (n + 2) (n + 1) n) x
  change ((underlyingBar k A).d (n + 1) n).hom
    (((underlyingBar k A).d (n + 2) (n + 1)).hom x) = 0 at h
  exact h

/-- The left-enveloping bar, using native ChainComplex.of and the same stored maps. -/
def envelopingBar : ChainComplex (ModuleCat.{max u v} (EnvelopingAlgebra k A)) ℕ :=
  ChainComplex.of (envelopingBarDegree k A) (envelopingBarBoundary k A)
    (envelopingBarBoundary_square k A)

/-- The enriched differential evaluates to the exact original differential. -/
theorem envelopingBar_d_apply (n : ℕ) (x : envelopingBarDegree k A (n + 1)) :
    ((envelopingBar k A).d (n + 1) n).hom x = ((underlyingBar k A).d (n + 1) n).hom x :=
  congrArg (fun f : envelopingBarDegree k A (n + 1) ⟶ envelopingBarDegree k A n => f.hom x)
    (ChainComplex.of_d (envelopingBarDegree k A) (envelopingBarBoundary k A) n)

/-- The native regular enveloping representation supplies the target module on A. -/
@[instance_reducible]
def regularEnvelopingModule : Module (EnvelopingAlgebra k A) A :=
  Module.compHom A (regularEnvelopingAction (k := k) (A := A)).toRingHom

/-- The multiplication augmentation intertwines the native regular action on A. -/
theorem underlyingBarAugmentation_intertwines (z : EnvelopingAlgebra k A) :
    (underlyingBarAugmentationLinear k A).comp (TensorPower.outerRepresentation k A 0 z) =
      (regularEnvelopingAction (k := k) (A := A) z).comp
        (underlyingBarAugmentationLinear k A) := by
  let f : (A ⊗[k] TensorPower k 1 A) →ₗ[k] A := underlyingBarAugmentationLinear k A
  have hf : ∀ (m : A) (a : Fin 1 → A), f (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m * a 0 := by
    intro m a
    exact underlyingBarAugmentationLinear_tprod k A m a
  induction z using TensorProduct.inductionOn with
  | tmul l r =>
      apply tensorPower_ext
        (f := f.comp (TensorPower.outerRepresentation k A 0 (l ⊗ₜ[k] r)))
        (g := (regularEnvelopingAction (k := k) (A := A) (l ⊗ₜ[k] r)).comp f)
      intro a₀ a
      simp only [LinearMap.comp_apply]
      have hout := TensorPower.outerModule_tprod k A 0 l r.unop a₀ a
      change TensorPower.outerRepresentation k A 0 (l ⊗ₜ[k] MulOpposite.op r.unop)
        (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) = _ at hout
      rw [MulOpposite.op_unop] at hout
      rw [hout, hf, hf]
      have hc : (Fin.snoc (α := fun _ : Fin 1 => A) (Fin.init a)
          (a (Fin.last 0) * r.unop)) 0 = a 0 * r.unop := by
        have hlast := Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => A)
          (x := a (Fin.last 0) * r.unop) (p := Fin.init a)
        change (Fin.snoc (α := fun _ : Fin 1 => A) (Fin.init a)
          (a (Fin.last 0) * r.unop)) 0 = a 0 * r.unop at hlast
        exact hlast
      simpa only [regularEnvelopingAction, AlgHom.mulLeftRight_apply, mul_assoc] using
        congrArg (fun c : A => l * (a₀ * c)) hc
  | add z w hz hw =>
      apply LinearMap.ext
      intro x
      change f (TensorPower.outerRepresentation k A 0 (z + w) x) =
        regularEnvelopingAction (k := k) (A := A) (z + w) (f x)
      rw [map_add, map_add]
      change f (TensorPower.outerRepresentation k A 0 z x +
        TensorPower.outerRepresentation k A 0 w x) =
          regularEnvelopingAction (k := k) (A := A) z (f x) +
            regularEnvelopingAction (k := k) (A := A) w (f x)
      exact (f.map_add _ _).trans
        (congrArg₂ (· + ·) (DFunLike.congr_fun hz x) (DFunLike.congr_fun hw x))

/-- Multiplication itself as an enveloping-linear map, retaining the original A carrier. -/
def envelopingAugmentationLinear :
    letI := TensorPower.outerModule k A 0
    letI := regularEnvelopingModule k A
    (A ⊗[k] TensorPower k 1 A) →ₗ[EnvelopingAlgebra k A] A := by
  let := TensorPower.outerModule k A 0
  let := regularEnvelopingModule k A
  exact {
    toFun := underlyingBarAugmentationLinear k A
    map_add' := (underlyingBarAugmentationLinear k A).map_add
    map_smul' := fun z x => by
      change underlyingBarAugmentationLinear k A (TensorPower.outerRepresentation k A 0 z x) =
        regularEnvelopingAction (k := k) (A := A) z (underlyingBarAugmentationLinear k A x)
      exact DFunLike.congr_fun (underlyingBarAugmentation_intertwines k A z) x }

/-- The original augmentation target, canonically lifted to the complex universe. -/
def regularEnvelopingTarget : ModuleCat.{max u v} (EnvelopingAlgebra k A) := by
  let := regularEnvelopingModule k A
  exact ModuleCat.of (EnvelopingAlgebra k A) (ULift.{max u v} A)

/-- The same multiplication augmentation into the regular enveloping target. -/
def envelopingBarAugmentation : (envelopingBar k A).X 0 ⟶ regularEnvelopingTarget k A := by
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k 1 A) :=
    TensorPower.outerModule k A 0
  let := regularEnvelopingModule k A
  exact ModuleCat.ofHom
    ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[EnvelopingAlgebra k A] ULift.{max u v} A).comp
      (envelopingAugmentationLinear k A))

/-- The canonical lift preserves the original augmentation value. -/
theorem envelopingBarAugmentation_apply (x : (envelopingBar k A).X 0) :
    (envelopingBarAugmentation k A).hom x = ULift.up (underlyingBarAugmentationLinear k A x) := by
  simp only [envelopingBarAugmentation]
  rfl

/-- The augmentation data law is inherited from the exact augmentation square. -/
theorem envelopingBar_d_augmentation :
    (envelopingBar k A).d 1 0 ≫ envelopingBarAugmentation k A = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  change (envelopingBarAugmentation k A).hom (((envelopingBar k A).d 1 0).hom x) = 0
  let F : (A ⊗[k] TensorPower k 1 A) →ₗ[k] A := underlyingBarAugmentationLinear k A
  have hD : (show A ⊗[k] TensorPower k 1 A from ((envelopingBar k A).d 1 0).hom x) =
      (show A ⊗[k] TensorPower k 1 A from ((underlyingBar k A).d 1 0).hom x) :=
    envelopingBar_d_apply k A 0 x
  have hc := congrArg (fun y : A ⊗[k] TensorPower k 1 A =>
    (ULift.up (F y) : ULift.{max u v} A)) hD
  have h := ConcreteCategory.congr_hom (underlyingBar_d_augmentation k A) x
  change ULift.up (F (((underlyingBar k A).d 1 0).hom x)) = 0 at h
  have ha := envelopingBarAugmentation_apply k A (((envelopingBar k A).d 1 0).hom x)
  change (envelopingBarAugmentation k A).hom (((envelopingBar k A).d 1 0).hom x) =
    (ULift.up (F (((envelopingBar k A).d 1 0).hom x)) : ULift.{max u v} A) at ha
  exact ha.trans (hc.trans h)

end ModuleCat.Algebra.Hochschild.AdjacentBar
